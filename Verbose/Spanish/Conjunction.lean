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
-/

open Lean

namespace Verbose.Spanish

section Conjunction
open Lean Parser

/-- Caracteres que pueden TERMINAR un término, de modo que una `y` posterior
es una conjunción. -/
def canEndTerm (c : Char) : Bool :=
  !c.isWhitespace && !"=<>≤≥≠+-*/^∈∉⊆∧∨→↔↦∘¬,;:(⟨[{|".contains c

/-- Caracteres que NO pueden EMPEZAR un término: si detrás de una supuesta
conjunción viene uno de estos, no era una conjunción. -/
def canStartTerm (c : Char) : Bool :=
  !c.isWhitespace && !"=<>≤≥≠+*/^∈∉⊆∧∨→↔↦∘,;:)⟩]}|".contains c

def isOpenBracket  (c : Char) : Bool := "(⟨[{".contains c
def isCloseBracket (c : Char) : Bool := ")⟩]}".contains c
/-- Caracteres que abren una cabecera de ligadura (`∀ y, ...`). -/
def isBinderHead   (c : Char) : Bool := "∀∃λΣΠ".contains c
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
  let rec wordEnd (p : String.Pos.Raw) : String.Pos.Raw :=
    if p ≥ stop then p else if isWordDelim (get p) then p else wordEnd (nextp p)
  let rec lineStartOf (q : String.Pos.Raw) : String.Pos.Raw :=
    if q.byteIdx == 0 then q
    else let pr := String.Pos.Raw.prev str q
         if get pr == '\n' then q else lineStartOf pr
  let colOf (q : String.Pos.Raw) : Nat := q.byteIdx - (lineStartOf q).byteIdx
  let indentAt (q : String.Pos.Raw) : Nat :=
    let ls := lineStartOf q
    let rec cnt (r : String.Pos.Raw) (n : Nat) : Nat :=
      if r ≥ stop then n
      else if (get r) == ' ' then cnt (nextp r) (n+1) else n
    cnt ls 0
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
      if ch == '"' then go (skipString nxt) depth inBinder true
      else if ch == '-' && nxt < stop && get nxt == '-' then go (skipLine nxt) depth inBinder lastEnd
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
               -- que la línea donde empieza el hecho; si no, es la táctica siguiente.
               && (colOf after > indentAt start || !crossesNewline e after)) then some p
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
