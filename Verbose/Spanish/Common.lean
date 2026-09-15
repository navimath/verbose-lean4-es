import Verbose.Tactics.Common
import Verbose.Spanish.Conjunction

open Lean

namespace Verbose.Spanish

declare_syntax_cat AndES

syntax ppSpace spanishY ppSpace : AndES
syntax ppSpace spanishE ppSpace : AndES

/-- ¿Contiene esta sintaxis un corte de conjunción (un nodo `AndES`)? -/
partial def hasConjSplit (stx : Syntax) : Bool :=
  if ((toString stx.getKind).splitOn "AndES").length > 1 then true
  else stx.getArgs.any hasConjSplit

open Lean in
/-- ¿Es este nodo una conjunción `AndES`? -/
def isAndESNode (stx : Syntax) : Bool :=
  ((toString stx.getKind).splitOn "AndES").length > 1

open Lean in
/-- El primer nodo `AndES` dentro de `stx`, si lo hay. -/
partial def findAndESNode (stx : Syntax) : Option Syntax :=
  if isAndESNode stx then some stx
  else stx.getArgs.findSome? findAndESNode

open Lean in
/-- La primera conjunción del árbol JUNTO CON el hermano que la precede.

Ese hermano es el primer miembro de la conjunción, y por tanto donde empieza el
grupo que hay que poner entre paréntesis. Sacarlo del árbol (en vez de recibirlo
como argumento) es lo que permite envolver CUALQUIER táctica sin saber cómo se
llama su nodo de hechos. -/
partial def findConjContext (stx : Syntax) : Option (Syntax × Syntax × Syntax) :=
  let args := stx.getArgs
  let rec scan (i : Nat) (prev : Option Syntax) : Option (Syntax × Syntax × Syntax) :=
    if i < args.size then
      let a := args[i]!
      if isAndESNode a then
        match prev with
        | some q => some (q, a, stx)
        | none   => scan (i+1) prev
      else
        match findConjContext a with
        | some r => some r
        | none   =>
          let prev' := if a.getRange?.isSome then some a else prev
          scan (i+1) prev'
    else none
  scan 0 none

open Lean Elab Tactic in
/-- Reconstruye la táctica poniendo entre paréntesis desde el principio del
primer hecho hasta la palabra que sigue a la conjunción. Es la corrección más
probable: la conjunción era en realidad un argumento. -/
def conjGroupText (tac : Syntax) : TacticM (Option String) := do
  let some (prev, andNode, parent) := findConjContext tac | return none
  let some factR := prev.getRange? | return none
  let some andR := andNode.getRange? | return none
  let some parR := parent.getRange? | return none
  let src := (← getFileMap).source
  let getc := String.Pos.Raw.get src
  let mut p := match findSep src factR.start parR.stop andR.stop.byteIdx with
    | some q => q
    | none   => parR.stop
  while p.byteIdx > factR.start.byteIdx && (getc (String.Pos.Raw.prev src p)).isWhitespace do
    p := String.Pos.Raw.prev src p
  if p.byteIdx ≤ factR.start.byteIdx then return none
  if p.byteIdx ≤ andR.stop.byteIdx then return none
  return some (String.Pos.Raw.extract src factR.start p)

open Lean Elab Tactic in
/-- Reconstruye la táctica ENTERA con el grupo entre paréntesis. Puede fallar
aunque `conjGroupText` funcione: si la táctica llegó por expansión de una macro
(`Afirmación ... ya que ...`), el rango de origen no cubre el texto que habría
que reescribir. En ese caso hay nota pero no botón. -/
def conjFixText (tac : Syntax) : TacticM (Option (String × String)) := do
  let some (prev, andNode, parent) := findConjContext tac | return none
  let some tacR := tac.getRange? | return none
  let some factR := prev.getRange? | return none
  let some andR := andNode.getRange? | return none
  let some parR := parent.getRange? | return none
  let src := (← getFileMap).source
  let getc := String.Pos.Raw.get src
  let nextc := String.Pos.Raw.next src
  -- El corte correcto es la SIGUIENTE conjunción candidata: todo lo que va antes
  -- pertenece al primer hecho.
  let mut p := match findSep src factR.start parR.stop andR.stop.byteIdx with
    | some q => q
    | none   => parR.stop
  -- recortar el espacio en blanco que quede antes del paréntesis de cierre
  while p.byteIdx > factR.start.byteIdx && (getc (String.Pos.Raw.prev src p)).isWhitespace do
    p := String.Pos.Raw.prev src p
  if p.byteIdx ≤ factR.start.byteIdx then return none
  -- El grupo tiene que TRAGARSE la conjunción. Si acaba antes, no arregla nada
  -- (envolver `0` en `(0)` no cambia nada) y la pista sería ruido.
  if p.byteIdx ≤ andR.stop.byteIdx then return none
  -- Si lo que íbamos a envolver YA es un grupo entre paréntesis, envolverlo otra
  -- vez sería absurdo (`((g y z) y P)`): significa que el corte problemático está
  -- en otro sitio y no sabemos arreglarlo.
  if getc factR.start == '(' then
    let mut q := factR.start
    let mut d := 0
    let mut cierre := factR.start
    while q.byteIdx < p.byteIdx do
      let c := getc q
      if "(⟨[{".contains c then d := d + 1
      else if ")⟩]}".contains c then
        d := d - 1
        if d == 0 && cierre.byteIdx == factR.start.byteIdx then cierre := q
      q := nextc q
    if cierre.byteIdx ≥ (String.Pos.Raw.prev src p).byteIdx then return none
  let pre := String.Pos.Raw.extract src tacR.start factR.start
  let mid := String.Pos.Raw.extract src factR.start p
  let post := String.Pos.Raw.extract src p tacR.stop
  let fixed := pre ++ "(" ++ mid ++ ")" ++ post
  -- COMPROBACIÓN: la sugerencia tiene que ser una táctica válida. Si el árbol de
  -- sintaxis venía incompleto (porque la táctica ni siquiera parseaba), `fixed`
  -- saldría truncado y aplicarlo BORRARÍA código del estudiante.
  match Lean.Parser.runParserCategory (← getEnv) `tactic fixed with
  | .error _ => return none
  | .ok _ => return some (fixed, mid)

open Lean Elab Tactic in
/-- ¿Tiene sentido este texto como término en el contexto actual?

Es la comprobación que da precisión a la pista: si `g y z` elabora, el
estudiante casi seguro quería una aplicación y la `y` se leyó mal. Si no
elabora (`P y Q` con `P` y `Q` proposiciones), el fallo es por otro motivo y no
hay que decir nada.

Hay que mirar tanto las excepciones como los errores REGISTRADOS: los numerales
elaboran de forma perezosa y sólo registran, sin lanzar. Los mensajes de la
comprobación se descartan para no duplicarlos. -/
def textElaborates (txt : String) : TacticM Bool := do
  let .ok stx := Lean.Parser.runParserCategory (← getEnv) `term txt | return false
  let msgs0 := (← getThe Core.State).messages
  let nErr (l : MessageLog) : Nat := (l.toList.filter (·.severity == .error)).length
  let n0 := nErr msgs0
  let ok ←
    try
      withMainContext do Term.withoutErrToSorry do
        discard <| Term.elabTerm stx none
        Term.synthesizeSyntheticMVarsNoPostponing
        return true
    catch _ => pure false
  let n1 := nErr (← getThe Core.State).messages
  modifyThe Core.State fun st => { st with messages := msgs0 }
  return ok && n1 == n0

open Lean Elab Tactic Lean.Meta.Tactic.TryThis in
/-- Número de errores en un registro de mensajes. -/
def numErrores (l : MessageLog) : Nat := (l.toList.filter (·.severity == .error)).length

open Lean Elab Tactic Lean.Meta.Tactic.TryThis in
/-- Decide POR ADELANTADO si procede una pista, y con qué texto.

Se calcula antes de ejecutar la táctica porque las tres condiciones (hay
conjunción, el grupo elabora, la corrección vuelve a parsear) no dependen de que
la táctica se ejecute. Saberlo antes permite NO envolver la táctica cuando no hay
nada que decir, que es justo lo que hace falta: ver la nota de `withConjHint`. -/
def conjHintData (stx : Syntax) : TacticM (Option (String × Option String)) := do
  unless hasConjSplit stx do return none
  let some grupo ← conjGroupText stx | return none
  unless ← textElaborates grupo do return none
  let fixed? ← do
    match ← conjFixText stx with
    | some (f, _) => pure (some f)
    | none        => pure none
  return some (s!"Nota: se ha leído una `y` (o una `e`) como conjunción, pero `{grupo}` sí tiene sentido como una sola expresión. Si esa palabra era en realidad un argumento, ponlo entre paréntesis: `(P y)` en vez de `P y`.", fixed?)

open Lean Elab Tactic Lean.Meta.Tactic.TryThis in
/-- Ejecuta `k` añadiendo una pista si el fallo viene de una conjunción mal leída.

Envolver una táctica en `try`/`catch` NO es inocuo: dentro de un `try` la
elaboración lanza en vez de registrar, y al capturar se deshace el estado, con el
registro de mensajes incluido. Envolviendo siempre, `Como A y Desconocido ...`
dejaba de dar «identificador desconocido» y salía como un `sorry` MUDO, que es
mucho peor que un error feo.

Por eso se decide antes: si no hay pista que dar, la táctica se ejecuta sin
tocarla. Sólo se envuelve cuando ya sabemos que hay algo que decir, y ahí se
relanza con `throwError` (no con `throw e`, que pierde el mensaje) y sin tocar
las excepciones internas, que son control de flujo de Lean. -/
def withConjHint {α : Type} (stx : Syntax) (k : TacticM α) : TacticM α := do
  match ← conjHintData stx with
  | none => k
  | some (nota, fixed?) =>
    let ofrece : TacticM Unit := do
      if let some f := fixed? then
        addSuggestion (← getRef) { suggestion := .string f } (header := "Prueba con: ")
    let n0 := numErrores (← getThe Core.State).messages
    try
      let a ← k
      -- algunas tácticas terminan «bien» y sólo registran el error
      if numErrores (← getThe Core.State).messages > n0 then
        ofrece
        logWarning nota
      return a
    catch e =>
      match e with
      | .internal _ _ => throw e
      | _ =>
        ofrece
        throwError "{e.toMessageData}\n\n{nota}"

declare_syntax_cat appliedToES
syntax "aplicado a " sepBy1(termUntilSep, ", ", AndES) : appliedToES

def appliedToESTerm : TSyntax `appliedToES → Array Term
| `(appliedToES| aplicado a $[$args],*) => args
| _ => default -- This will never happen as long as nobody extends appliedToES


declare_syntax_cat usingStuffES
syntax " usando " sepBy1(termUntilSep, ", ", AndES) : usingStuffES
syntax " usando que " term : usingStuffES

def usingStuffESToTerm : TSyntax `usingStuffES → Array Term
| `(usingStuffES| usando $[$args],*) => args
| `(usingStuffES| usando que $x) => #[Unhygienic.run `(strongAssumption% $x)]
| _ => default -- This will never happen as long as nobody extends appliedToES

declare_syntax_cat maybeAppliedES
syntax termUntilSep (appliedToES)? (usingStuffES)? : maybeAppliedES

def maybeAppliedESToTerm : TSyntax `maybeAppliedES → MetaM Term
| `(maybeAppliedES| $e:term) => pure e
| `(maybeAppliedES| $e:term $args:appliedToES) => `($e $(appliedToESTerm args)*)
| `(maybeAppliedES| $e:term $args:usingStuffES) => `($e $(usingStuffESToTerm args)*)
| `(maybeAppliedES| $e:term $args:appliedToES $extras:usingStuffES) =>
  `($e $(appliedToESTerm args)* $(usingStuffESToTerm extras)*)
| _ => pure default -- This will never happen as long as nobody extends maybeAppliedES

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
and the second one is its main arguments. When there is a third element, it is assumed
to be the type of a prop argument. -/
def listTermToMaybeApplied : List Term → MetaM (TSyntax `maybeAppliedES)
| [x] => `(maybeAppliedES|$x:term)
| [x, v] => `(maybeAppliedES|$x:term aplicado a $v)
| [x, v, z] => `(maybeAppliedES|$x:term aplicado a $v usando que $z)
| x::v::l => `(maybeAppliedES|$x:term aplicado a $v:term usando [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuffES
syntax (ppSpace colGt maybeTypedIdent)* : newStuffES
syntax maybeTypedIdent "tal que" ppSpace colGt maybeTypedIdent : newStuffES
syntax maybeTypedIdent "tal que" ppSpace colGt maybeTypedIdent AndES
       colGt maybeTypedIdent : newStuffES

def newStuffESToArray : TSyntax `newStuffES → Array MaybeTypedIdent
| `(newStuffES| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffES| $x:maybeTypedIdent tal que $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuffES| $x:maybeTypedIdent tal que $v:maybeTypedIdent $_and:AndES $z) =>
    Array.map toMaybeTypedIdent #[x, v, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatES : List MaybeTypedIdent → MetaM (TSyntax `newStuffES)
| [x] => do `(newStuffES| $(← x.stx):maybeTypedIdent)
| [x, z] => do `(newStuffES| $(← x.stx):maybeTypedIdent tal que $(← z.stx'))
| [x, z, y] => do `(newStuffES| $(← x.stx):maybeTypedIdent tal que $(← z.stx) y $(← y.stx))
| _ => pure default

declare_syntax_cat newFactsES
syntax colGt namedType : newFactsES
syntax colGt namedType AndES colGt namedType : newFactsES
syntax colGt namedType ", "  colGt namedType AndES colGt namedType : newFactsES

def newFactsESToArray : TSyntax `newFactsES → Array NamedType
| `(newFactsES| $x:namedType) => #[toNamedType x]
| `(newFactsES| $x:namedType $_and:AndES $v:namedType) =>
    #[toNamedType x, toNamedType v]
| `(newFactsES| $x:namedType, $v:namedType $_and:AndES $z:namedType) =>
    #[toNamedType x, toNamedType v, toNamedType z]
| _ => #[]

def newFactsESToTypeTerm : TSyntax `newFactsES → MetaM Term
| `(newFactsES| $x:namedType) => do
    namedTypeToTypeTerm x
| `(newFactsES| $x:namedType $_and:AndES $v) => do
    let xT ← namedTypeToTypeTerm x
    let vT ← namedTypeToTypeTerm v
    `($xT ∧ $vT)
| `(newFactsES| $x:namedType, $v:namedType $_and:AndES $z) => do
    let xT ← namedTypeToTypeTerm x
    let vT ← namedTypeToTypeTerm v
    let zT ← namedTypeToTypeTerm z
    `($xT ∧ $vT ∧ $zT)
| _ => throwError "No se ha podido convertir la información dada en un término."

open Tactic Lean.Elab.Tactic.RCases in
def newFactsESToRCasesPatt : TSyntax `newFactsES → RCasesPatt
| `(newFactsES| $x:namedType) => namedTypeListToRCasesPatt [x]
| `(newFactsES| $x:namedType $_and:AndES $v:namedType) => namedTypeListToRCasesPatt [x, v]
| `(newFactsES|  $x:namedType, $v:namedType $_and:AndES $z:namedType) => namedTypeListToRCasesPatt [x, v, z]
| _ => default

def listMaybeTypedIdentToNewFactsES : List MaybeTypedIdent → MetaM (TSyntax `newFactsES)
| [x] => do `(newFactsES| $(.mk (← x.stx)))
| [x, v] => do `(newFactsES| $(.mk (← x.stx).raw):namedType y $(.mk (← v.stx)))
| [x, v, z] => do `(newFactsES| $(.mk (← x.stx)):namedType, $(.mk (← v.stx)) y $(.mk (← z.stx)))
| _ => pure default

syntax talesQue := "tal que " <|> "tales que "

declare_syntax_cat newObjectES
syntax maybeTypedIdent "tal que " maybeTypedIdent : newObjectES
syntax maybeTypedIdent "tal que " maybeTypedIdent colGt AndES maybeTypedIdent : newObjectES
syntax maybeTypedIdent "tal que " maybeTypedIdent ", " colGt maybeTypedIdent colGt AndES maybeTypedIdent : newObjectES

syntax maybeTypedIdent AndES maybeTypedIdent "tal que " maybeTypedIdent : newObjectES
syntax maybeTypedIdent AndES maybeTypedIdent "tal que " maybeTypedIdent colGt AndES maybeTypedIdent : newObjectES
syntax maybeTypedIdent AndES maybeTypedIdent "tal que " maybeTypedIdent ", " colGt maybeTypedIdent colGt AndES maybeTypedIdent : newObjectES

def newObjectESToTerm : TSyntax `newObjectES → MetaM Term
| `(newObjectES| $x:maybeTypedIdent tal que $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObjectES| $x:maybeTypedIdent tal que $new₁ $_and:AndES $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| `(newObjectES| $x:maybeTypedIdent tal que $new₁, $new₂ $_and:AndES $new₃) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    let new₃T := (toMaybeTypedIdent new₃).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T ∧ $new₃T)
| `(newObjectES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let v' ← maybeTypedIdentToExplicitBinder v
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), ∃ $(.mk v'), $newT)
| `(newObjectES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new₁ $_and':AndES $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let v' ← maybeTypedIdentToExplicitBinder v
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), ∃ $(.mk v'), $new₁T ∧ $new₂T)
| `(newObjectES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new₁, $new₂ $_and':AndES $new₃) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let v' ← maybeTypedIdentToExplicitBinder v
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    let new₃T := (toMaybeTypedIdent new₃).2.get!
    `(∃ $(.mk x'), ∃ $(.mk v'), $new₁T ∧ $new₂T ∧ $new₃T)
| _ => throwError "No se ha podido convertir la descripción del objeto nuevo en un término."

def newObjectESToMaybeTypedIdentList : TSyntax `newObjectES → List (TSyntax `maybeTypedIdent)
| `(newObjectES| $x:maybeTypedIdent tal que $new) => [x, new]
| `(newObjectES| $x:maybeTypedIdent tal que $new₁ $_and:AndES $new₂) => [x, new₁, new₂]
| `(newObjectES| $x:maybeTypedIdent tal que $new₁, $new₂ $_and:AndES $new₃) => [x, new₁, new₂, new₃]
| `(newObjectES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new) => [x, v, new]
| `(newObjectES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new₁ $_and':AndES $new₂) => [x, v, new₁, new₂]
| `(newObjectES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new₁, $new₂ $_and':AndES $new₃) => [x, v, new₁, new₂, new₃]
| _ => []


def newObjectESToArray : TSyntax `newObjectES → Array MaybeTypedIdent
| `(newObjectES| $x:maybeTypedIdent tal que $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newObjectES| $x:maybeTypedIdent tal que $v:maybeTypedIdent $_and:AndES $z) =>
    Array.map toMaybeTypedIdent #[x, v, z]
| _ => #[]

open Tactic Lean.Elab.Tactic.RCases in
def newObjectESToRCasesPatt (newObj : TSyntax `newObjectES) : RCasesPatt :=
  maybeTypedIdentListToRCasesPatt <| newObjectESToMaybeTypedIdentList newObj

-- FIXME: the code below is ugly, written in a big hurry.
def listMaybeTypedIdentToNewObjectES : List MaybeTypedIdent → MetaM (TSyntax `newObjectES)
| [x, v] => do `(newObjectES| $(← x.stx):maybeTypedIdent tal que $(← v.stx'))
| [x, v, z] => do `(newObjectES| $(← x.stx):maybeTypedIdent tal que $(← v.stx) y $(← z.stx))
| _ => pure default

declare_syntax_cat factsES
syntax term : factsES
syntax termUntilSep AndES term : factsES
syntax termUntilSep ", " termUntilSep AndES term : factsES
syntax termUntilSep ", " termUntilSep ", " termUntilSep AndES term : factsES

def factsESToArray : TSyntax `factsES → Array Term
| `(factsES| $x:term) => #[x]
| `(factsES| $x:term $_and:AndES $v:term) => #[x, v]
| `(factsES| $x:term, $v:term $_and:AndES $z:term) => #[x, v, z]
| `(factsES| $x:term, $v:term, $z:term $_and:AndES $w:term) => #[x, v, z, w]
| _ => #[]

def arrayToFactsES : Array Term → CoreM (TSyntax `factsES)
| #[x] => `(factsES| $x:term)
| #[x, v] => `(factsES| $x:term y $v:term)
| #[x, v, z] => `(factsES| $x:term, $v:term y $z:term)
| #[x, v, z, w] => `(factsES| $x:term, $v:term, $z:term y $w:term)
| _ => default

def factsESToTypeTerm : TSyntax `factsES → MetaM Term
| `(factsES| $x:term) => `($x)
| `(factsES| $x:term $_and:AndES $v) => `($x ∧ $v)
| `(factsES| $x:term, $v:term $_and:AndES $z) => `($x ∧ $v ∧ $z)
| _ => throwError "No se ha podido convertir la información dada en un término.."

/-- Convert an expression to a `maybeAppliedES` syntax object, in `MetaM`. -/
def _root_.Lean.Expr.toMaybeAppliedES (e : Expr) : MetaM (TSyntax `maybeAppliedES) := do
  let fn := e.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match e.getAppArgs.toList with
  | [] => `(maybeAppliedES|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeAppliedES|$fnS:term aplicado a $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeAppliedES|$fnS:term aplicado a [$arr:term,*])

declare_syntax_cat newObjectNameLessES
syntax maybeTypedIdent "tal que " term : newObjectNameLessES
syntax maybeTypedIdent "tal que " termUntilSep colGt AndES term : newObjectNameLessES
syntax maybeTypedIdent "tal que " termUntilSep ", " colGt termUntilSep colGt AndES term : newObjectNameLessES

syntax maybeTypedIdent AndES maybeTypedIdent "tal que " term : newObjectNameLessES
syntax maybeTypedIdent AndES maybeTypedIdent "tal que " termUntilSep colGt AndES term : newObjectNameLessES
syntax maybeTypedIdent AndES maybeTypedIdent "tal que " termUntilSep ", " colGt termUntilSep colGt AndES term : newObjectNameLessES

def newObjectNameLessESToLists : TSyntax `newObjectNameLessES → (List (TSyntax `maybeTypedIdent) × List Term)
| `(newObjectNameLessES| $x:maybeTypedIdent tal que $new) =>
  ([x], [new])
| `(newObjectNameLessES| $x:maybeTypedIdent tal que $new₁ $_and:AndES $new₂) =>
  ([x], [new₁, new₂])
| `(newObjectNameLessES| $x:maybeTypedIdent tal que $new₁, $new₂ $_and:AndES $new₃) =>
  ([x], [new₁, new₂, new₃])
| `(newObjectNameLessES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new) =>
  ([x, v], [new])
| `(newObjectNameLessES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new₁ $_and':AndES $new₂) =>
  ([x, v], [new₁, new₂])
| `(newObjectNameLessES| $x:maybeTypedIdent $_and:AndES $v:maybeTypedIdent tal que $new₁, $new₂ $_and':AndES $new₃) =>
  ([x, v], [new₁, new₂, new₃])
| _ => default

def newObjectNameLessESToTerm (no : TSyntax `newObjectNameLessES) : MetaM Term :=
  let (xs, news) := newObjectNameLessESToLists no
  newObjNlToTerm xs news

def newObjectNameLessESToArray (no : TSyntax `newObjectNameLessES) : Array MaybeTypedIdent :=
  let (xs, news) := newObjectNameLessESToLists no
  newObjNlToArray xs news

open Tactic Lean.Elab.Tactic.RCases in
def newObjectNameLessESToRCasesPatt (no : TSyntax `newObjectNameLessES) : RCasesPatt :=
  let (xs, news) := newObjectNameLessESToLists no
  newObjNlToRCasesPatt xs news

def listMaybeTypedIdentToNewObjectNameLessES : List MaybeTypedIdent → MetaM (TSyntax `newObjectNameLessES)
| [(x, some t), (_, some s)] => do `(newObjectNameLessES| ($(mkIdent x):ident : $t) tal que $s)
| [(x, none), (_, some s)] => do `(newObjectNameLessES| $(mkIdent x):ident tal que $s)
| [(x, none), (_, some s), (_, some r)] => do `(newObjectNameLessES| $(mkIdent x):ident tal que $s y $r)
| [(x, some t), (_, some s), (_, some r)] => do `(newObjectNameLessES| ($(mkIdent x):ident : $t) tal que $s y $r)
| _ => pure default

implement_endpoint (lang := es) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"El nombre {n} ya está en uso"

implement_endpoint (lang := es) notDefEq (e val : MessageData) : CoreM MessageData :=
pure m!"El término {e}\n no es igual por definición a {val}"

implement_endpoint (lang := es) notAppConst : CoreM String :=
pure "No es la aplicación de una definición."

implement_endpoint (lang := es) cannotExpand : CoreM String :=
pure "No se ha podido expandir la cabeza del término."

implement_endpoint (lang := es) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"La afirmación {tgt} no parece directamente derivable de ninguna hipótesis local por sí sola."

implement_endpoint (lang := es) couldNotProve (goal : Format) : CoreM String :=
pure s!"No se pudo probar:\n{goal}"

implement_endpoint (lang := es) failedProofUsing (goal : Format) : CoreM String :=
pure s!"Con la información dada, no se ha podido probar:\n{goal}"
