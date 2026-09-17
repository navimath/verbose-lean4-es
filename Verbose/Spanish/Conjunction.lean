import Verbose.Tactics.Common

/-!
# La conjunción española `y` / `e`

En español, `y` es un nombre de variable muy común, así que no se puede
reservar como palabra clave (a diferencia del inglés `and` o el francés `et`).

La regla que implementamos aquí es:

* en general, `y` es un término (un identificador normal);
* EXCEPTO cuando viene precedido por algo que puede terminar un término,
  a profundidad de paréntesis 0 y fuera de una cabecera de ligadura
  (`∀ y, ...`), en cuyo caso es la conjunción.

Como esta condición se puede decidir léxicamente, la aplicamos ANTES de
llamar al parser de términos: `findSep` busca el punto de corte y
`termUntilSep` trunca `endPos` ahí, de modo que el parser de términos nunca
llega a ver la `y`. Así los ligadores (`∀ (y : ℕ), ...`) siguen funcionando
y no se toca la tabla global de tokens, por lo que el inglés y el francés
no se ven afectados.

El escáner reconoce como «no código» las cadenas, los comentarios de línea
(`--`) y los de bloque (`/- -/`, anidados incluidos), y nunca sale del bloque
de la táctica: se detiene en la primera línea que vuelve a la sangría del
hecho o por debajo. Eso último no es sólo una cuestión de coste: una `y` de la
táctica SIGUIENTE no puede ser la conjunción de ésta.
-/

open Lean

namespace Verbose.Spanish

section Conjunction
open Lean Parser

/-- Caracteres que pueden TERMINAR un término, de modo que una `y` posterior
es una conjunción.

`|` NO está en la lista: a profundidad 0 una barra sólo puede cerrar un valor
absoluto (`|u n - l|`), porque la barra del constructor de conjuntos
(`{y | y = y}`) va siempre dentro de llaves, o sea a profundidad ≥ 1. Y al
salir de un paréntesis `lastEnd` ya se pone a `true` de todos modos. -/
def canEndTerm (c : Char) : Bool :=
  !c.isWhitespace && !"=<>≤≥≠+-*/^∈∉⊆∧∨→↔↦∘¬,;:(⟨[{".contains c

/-- Caracteres que NO pueden EMPEZAR un término: si detrás de una supuesta
conjunción viene uno de estos, no era una conjunción.

Tampoco está `|`, por el mismo motivo: `y |x| = 1` abre un valor absoluto. -/
def canStartTerm (c : Char) : Bool :=
  !c.isWhitespace && !"=<>≤≥≠+*/^∈∉⊆∧∨→↔↦∘,;:)⟩]}".contains c

def isOpenBracket  (c : Char) : Bool := "(⟨[{".contains c
def isCloseBracket (c : Char) : Bool := ")⟩]}".contains c

/-- Caracteres que abren una cabecera de ligadura, donde una `y` es una
variable ligada y nunca una conjunción.

Además de los ligadores propiamente dichos (`∀ ∃ λ Σ Π`), los operadores
grandes ligan variables: sin `⋃` en la lista, `s = ⋃ y z, S y z` se cortaba
por la `y` LIGADA, que no es ni siquiera un caso diagnosticable. -/
def isBinderHead   (c : Char) : Bool := "∀∃λΣΠ∑∏⋃⋂⨆⨅⨁⨂".contains c

/-- Caracteres que van delante del código de una línea sin ser código: espacio,
tabulador y el foco de táctica (`· ...`).

Contar el foco importa: en `· Como ... y` la sangría efectiva de la táctica no
es la de los espacios iniciales, sino la de la `C` de `Como`. Si no, el cuerpo
de la viñeta parece MÁS indentado que su propia línea y la táctica siguiente se
cuela como segundo miembro de la conjunción. -/
def isIndentChar   (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '·' || c == '.'

def isWordDelim    (c : Char) : Bool :=
  c.isWhitespace || isOpenBracket c || isCloseBracket c || c == ',' || c == '"'

/-- ¿Es `w` una de las conjunciones españolas? -/
def isConjWord (w : String) : Bool := w == "y" || w == "e"

/-- Busca un separador (`y` o `e`): una PALABRA suelta, a profundidad 0,
fuera de cadenas y comentarios, fuera de una cabecera de ligadura, y
precedida por algo que puede terminar un término. -/
partial def findSep (str : String) (start stop : String.Pos.Raw) (minByte : Nat := 0) :
    Option String.Pos.Raw :=
  let get := String.Pos.Raw.get str
  let nextp := String.Pos.Raw.next str
  let rec skipString (p : String.Pos.Raw) : String.Pos.Raw :=
    if p ≥ stop then p
    else if get p == '\\' then skipString (nextp (nextp p))
    else if get p == '"' then nextp p
    else skipString (nextp p)
  let rec skipLine (p : String.Pos.Raw) : String.Pos.Raw :=
    if p ≥ stop then p else if get p == '\n' then p else skipLine (nextp p)
  -- Comentario de bloque, con anidamiento. `p` va justo detrás del `/-` de
  -- apertura y `level` cuenta los comentarios abiertos. Hay que mirarlo ANTES
  -- que las comillas: un `"` suelto dentro de un comentario mandaba
  -- `skipString` hasta el final del fichero.
  let rec skipBlock (p : String.Pos.Raw) (level : Nat) : String.Pos.Raw :=
    if p ≥ stop then p
    else
      let nx := nextp p
      if get p == '/' && nx < stop && get nx == '-' then skipBlock (nextp nx) (level+1)
      else if get p == '-' && nx < stop && get nx == '/' then
        if level ≤ 1 then nextp nx else skipBlock (nextp nx) (level-1)
      else skipBlock nx level
  let rec wordEnd (p : String.Pos.Raw) : String.Pos.Raw :=
    if p ≥ stop then p else if isWordDelim (get p) then p else wordEnd (nextp p)
  let rec lineStartOf (q : String.Pos.Raw) : String.Pos.Raw :=
    if q.byteIdx == 0 then q
    else let pr := String.Pos.Raw.prev str q
         if get pr == '\n' then q else lineStartOf pr
  let colOf (q : String.Pos.Raw) : Nat := q.byteIdx - (lineStartOf q).byteIdx
  let rec skipIndent (r : String.Pos.Raw) : String.Pos.Raw :=
    if r ≥ stop then r else if isIndentChar (get r) then skipIndent (nextp r) else r
  -- Sangría efectiva de la línea de `q`: dónde empieza el código de verdad.
  let indentAt (q : String.Pos.Raw) : Nat :=
    let ls := lineStartOf q
    (skipIndent ls).byteIdx - ls.byteIdx
  let baseIndent := indentAt start
  -- ¿La línea que empieza en `p` se sale ya del bloque de la táctica?
  -- Las líneas en blanco no cuentan.
  let rec leavesBlock (p : String.Pos.Raw) : Bool :=
    if p ≥ stop then true
    else
      let r := skipIndent p
      if r ≥ stop then true
      else if get r == '\n' then leavesBlock (nextp r)
      else r.byteIdx - p.byteIdx ≤ baseIndent
  let rec crossesNewline (a b : String.Pos.Raw) : Bool :=
    if a ≥ b then false
    else if get a == '\n' then true
    else crossesNewline (nextp a) b
  let rec go (p : String.Pos.Raw) (depth : Nat) (inBinder : Bool) (lastEnd : Bool) :
      Option String.Pos.Raw :=
    if p ≥ stop then none
    else
      let ch := get p
      let nxt := nextp p
      if ch == '/' && nxt < stop && get nxt == '-' then
        -- los comentarios son espacio en blanco: `lastEnd` se conserva
        go (skipBlock (nextp nxt) 1) depth inBinder lastEnd
      else if ch == '"' then go (skipString nxt) depth inBinder true
      else if ch == '-' && nxt < stop && get nxt == '-' then go (skipLine nxt) depth inBinder lastEnd
      else if ch == '\n' then
        -- Si la línea siguiente vuelve a la sangría del hecho, se ha acabado la
        -- táctica: ninguna `y` posterior podría aceptarse ya, así que paramos.
        -- Sin esto el escáner llegaba hasta el final del FICHERO.
        --
        -- `inBinder` NO se reinicia aquí: una cabecera de ligadura puede partirse
        -- en dos líneas (`∀ x⏎ y z : ℕ, ...`) y entonces la `y` de la segunda
        -- sigue siendo una variable ligada. Reiniciarlo cortaba justo ahí.
        -- No hace falta: toda cabecera se cierra con `,`, `=>` o `↦`.
        if leavesBlock nxt then none else go nxt depth inBinder lastEnd
      else if isOpenBracket ch then go nxt (depth+1) inBinder false
      else if isCloseBracket ch then go nxt (depth-1) inBinder true
      else if ch.isWhitespace then go nxt depth inBinder lastEnd
      else if ch == ',' then go nxt depth false false
      else if isBinderHead ch then go nxt depth true false
      else
        let e := wordEnd p
        let w := String.Pos.Raw.extract str p e
        if isConjWord w && p.byteIdx > minByte && depth == 0 && !inBinder && lastEnd
           && (let rec skipWs (q : String.Pos.Raw) : String.Pos.Raw :=
                 if q ≥ stop then q
                 else if (get q).isWhitespace then skipWs (nextp q) else q
               let after := skipWs e
               after < stop && canStartTerm (get after)
               -- Si el segundo miembro salta de línea, tiene que ir MÁS indentado
               -- que el hecho; si no, es la táctica siguiente.
               && (colOf after > baseIndent || !crossesNewline e after)) then some p
        else
          let lastCh := if e > p then get (String.Pos.Raw.prev str e) else ch
          -- `fun` abre una cabecera de ligadura; `=>` y `↦` la cierran
          -- (también cierran la de `λ`, que se detecta por carácter).
          let inBinder' :=
            if w == "fun" then true
            else if w == "=>" || w == "↦" then false
            else inBinder
          go e depth inBinder' (canEndTerm lastCh)
  go start 0 false false

/-- Un término que se detiene justo antes de una conjunción `y` / `e`. -/
def termUntilSep : Parser where
  info := (termParser : Parser).info
  fn := fun c s =>
    match findSep c.inputString s.pos c.endPos with
    | none   => (termParser : Parser).fn c s
    | some p =>
      if h : p ≤ c.inputString.rawEndPos then
        (termParser : Parser).fn (c.setEndPos p h) s
      else (termParser : Parser).fn c s

open PrettyPrinter in
@[combinator_formatter termUntilSep]
def termUntilSep.formatter : Formatter := Formatter.categoryParser.formatter `term

open PrettyPrinter in
@[combinator_parenthesizer termUntilSep]
def termUntilSep.parenthesizer : Parenthesizer := Parenthesizer.categoryParser.parenthesizer `term 0

/-- `y`, sin reservar el token. -/
@[run_parser_attribute_hooks]
def spanishY : Parser := nonReservedSymbol "y" (includeIdent := true)
/-- `e`, la variante de `y` ante palabras que empiezan por i- o hi-. -/
@[run_parser_attribute_hooks]
def spanishE : Parser := nonReservedSymbol "e" (includeIdent := true)

end Conjunction
