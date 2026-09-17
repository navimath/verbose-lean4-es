# La conjunción `y` / `e` en la versión española

## El problema

El inglés declara su conjunción como un átomo normal:

```lean
syntax "applied to " sepBy(term, " and ") : appliedTo
```

Eso reserva el token `and`. A partir de ahí `and` no se puede usar como nombre
de variable en ningún sitio: `example (and : ℕ) := ...` es un error de sintaxis.
El francés hace lo mismo con `et`.

En español la conjunción es `y`, que es uno de los nombres de variable más
frecuentes en matemáticas. Reservarla rompería el propio banco de pruebas
(`By.lean` usa `∀ (y : ℕ), g y ∈ A`).

La solución anterior era escribir `,y` y `,e`: la coma obliga al parser de
términos a parar, así que `y` no hace falta reservarla. El coste es una coma que
no se dice al leer en voz alta y que los estudiantes no entienden.

Este cambio quita `,y` y `,e` y deja `y` y `e` a secas.

## La regla

`y` es la conjunción cuando:

1. viene precedida de algo que puede TERMINAR un término, a profundidad de
   paréntesis 0 y fuera de una cabecera de ligadura (`∀ ∃ λ Σ Π`, `fun`, hasta
   `,`, `=>` o `↦`);
2. detrás viene algo que puede EMPEZAR un término;
3. si el segundo miembro salta de línea, va más indentado que el hecho.

En cualquier otro caso `y` es un identificador normal.

La condición se decide LÉXICAMENTE, antes de llamar al parser de términos. Ese
es el punto clave: el parser de términos es voraz y se tragaría la `y` como
argumento de una aplicación, así que hay que cortarle el paso antes.

---

## Ficheros nuevos

### `Conjunction.lean` (144 líneas, nuevo)

Implementa la regla. Tres piezas:

**`findSep`** recorre el texto y devuelve la posición del separador. Lleva tres
estados: profundidad de paréntesis, si estamos dentro de una cabecera de
ligadura, y si el último token puede terminar un término. Salta cadenas y
comentarios de línea. Compara PALABRAS, no caracteres: sin eso, `hy y n₀` se
partía dentro del identificador `hy`.

**`termUntilSep`** es el parser de términos con el corte aplicado:

```lean
def termUntilSep : Parser where
  info := (termParser : Parser).info
  fn := fun c s =>
    match findSep c.inputString s.pos c.endPos with
    | none   => (termParser : Parser).fn c s
    | some p =>
      if h : p ≤ c.inputString.rawEndPos then
        (termParser : Parser).fn (c.setEndPos p h) s
      else (termParser : Parser).fn c s
```

`setEndPos` recorta el final del contexto antes de llamar al parser de términos,
de modo que éste NUNCA llega a ver la `y`. Por eso los ligadores (`∀ (y : ℕ)`)
siguen funcionando y la tabla global de tokens no se toca: el inglés y el
francés no se enteran de nada.

Se probaron antes dos alternativas que no valen:

* `nonReservedSymbol "y"` a secas: el parser de términos se traga la `y` igual,
  porque para él es un identificador válido;
* meter `y` en la tabla de tokens localmente y usar `withForbidden`: funciona
  para el separador, pero entonces `∀ (y : ℕ)` deja de parsear DENTRO del
  operando, porque `withoutForbidden` (lo que usan los paréntesis) reinicia la
  bandera pero no la tabla de tokens.

**Formateador y parentetizador.** Un parser propio no sabe imprimirse:

```lean
@[combinator_formatter termUntilSep]
def termUntilSep.formatter : Formatter := Formatter.categoryParser.formatter `term
```

Sin esto Lean da `don't know how to generate formatter`. Hace falta de verdad:
todo `Help.lean` son sugerencias impresas.

`spanishY` y `spanishE` llevan `@[run_parser_attribute_hooks]`, necesario para
parsers definidos en un módulo importado.

### `Exceptions.lean` (432 líneas, nuevo)

Lo que sigue fallando, con 40 ejemplos compilados. Compila, así que es un test
de regresión: si una sugerencia deja de ser correcta, deja de compilar.

---

## Ficheros modificados

### `Common.lean` (+225 líneas)

**Declaraciones de sintaxis.** `term` pasa a `termUntilSep` allí donde una
conjunción puede separar términos:

```lean
-syntax "aplicado a " sepBy1(term, ",", AndES) : appliedToES
+syntax "aplicado a " sepBy1(termUntilSep, ", ", AndES) : appliedToES
```

Igual en `usingStuffES`, `maybeAppliedES`, las tres formas de `factsES` y las de
`newObjectNameLessES`. `maybeAppliedES` se pasó por alto al principio y por eso
`Calc.lean` fallaba: su término inicial era voraz.

**El átomo de la conjunción:**

```lean
-syntax " ,y " : AndES
+syntax ppSpace spanishY ppSpace : AndES
```

Los `ppSpace` son sólo para imprimir. Sin ellos la ayuda salía
`(n_pos : n > 0)y (hn : P n)`. Al añadirlos hubo que quitar el `ppSpace` que ya
había detrás de `AndES` en `newStuffES`, que si no salía doble.

**Diagnóstico.** Cuando la regla se equivoca (ver abajo), el error es
incomprensible. Estas funciones lo explican:

* `findConjContext` busca la primera conjunción del árbol y devuelve también el
  hermano anterior y el nodo padre. El hermano anterior es donde empieza el
  grupo que hay que poner entre paréntesis. Sacarlo del ÁRBOL, en vez de
  recibirlo como argumento, es lo que permite envolver cualquier táctica sin
  saber cómo se llama su nodo de hechos.
* `conjGroupText` devuelve el texto de ese grupo, hasta la SIGUIENTE conjunción
  candidata. Hasta la siguiente palabra no vale: daba `(g y z) w` en vez de
  `(g y z w)`.
* `conjFixText` reconstruye la táctica entera con el grupo entre paréntesis, y
  comprueba que el resultado vuelva a parsear como táctica. Esa comprobación no
  es cosmética: cuando la táctica no parseaba, el árbol venía incompleto y la
  sugerencia salía truncada; pulsar [apply] habría BORRADO el resto de la línea.
* `textElaborates` comprueba si un texto tiene sentido como término. Es lo que
  da precisión: si `g y z` elabora, el estudiante quería una aplicación. Si no
  (`P y Q` con `P` y `Q` proposiciones), el fallo es por otro motivo y no se dice
  nada. Mira excepciones Y errores registrados: los numerales (`3 y P`) elaboran
  de forma perezosa y sólo registran, sin lanzar.
* `conjHintData` decide POR ADELANTADO si procede una pista y con qué texto. Las
  tres condiciones son sintácticas o independientes de ejecutar la táctica, así
  que se pueden comprobar antes.
* `withConjHint` envuelve una táctica, pero SÓLO si `conjHintData` dice que hay
  algo que decir. Si no, ejecuta la táctica sin tocarla.

  Esa distinción no es una optimización, es correctitud. Envolver en
  `try`/`catch` no es inocuo: dentro de un `try` la elaboración lanza en vez de
  registrar, y al capturar se deshace el estado, registro de mensajes incluido.
  Envolviendo siempre, `Como A y Desconocido concluimos que ...` dejaba de dar
  «identificador desconocido» y salía como un `sorry` MUDO. El ejemplo compilaba
  con un agujero y nadie se enteraba.

  Cuando sí se envuelve, se relanza con `throwError` (no con `throw e`, que
  pierde el mensaje) y no se tocan las excepciones `.internal`, que son control
  de flujo de Lean y no errores. Vigila además DOS formas de fallar: la excepción
  lanzada y el caso en que la táctica «termina bien» pero deja errores
  registrados; sin lo segundo, `Por ... aplicado a ... tenemos ...` se quedaba
  sin pista.

### `Since.lean` (6 sitios), `By.lean` (4), `We.lean` (2), `Assume.lean` (2), `Calc.lean` (1)

Cada táctica queda envuelta:

```lean
-  sinceConcludeTac concl factsT
+  withConjHint (← getRef) <| sinceConcludeTac concl factsT
```

Detalles por fichero:

* **`By.lean`** y **`We.lean`**: al cambiar `term` por `termUntilSep` en un
  `sepBy1`, los elementos dejan de tener el tipo `Term`, y hay que convertirlos:
  `args.getElems.map fun s => (⟨s.raw⟩ : Term)`.
* **`Assume.lean`**: su sintaxis vive en `namespace Verbose.NameLess`, así que
  `termUntilSep` y `withConjHint` van cualificados con `Verbose.Spanish.`.
* **`Calc.lean`**: se envuelve `comoCalcTac`. La sugerencia con botón no se puede
  calcular aquí (ver más abajo), pero la nota sí sale.
* **`Claim.lean`**: no se toca. Sus formas `ya que` y `pues` son MACROS que se
  expanden a `Como ... concluimos que ...` y `Concluimos por ...`, que ya están
  envueltas.

### `Help.lean`, `Examples.lean`, `Claim.lean`

Sólo cambia el texto: `,y` a ` y `, `,e` a ` e `. 141 sitios en total
(Help 52, Since 46, Examples 14, Common 11, By 6, We 5, Calc 3, Assume 2,
Claim 2).

En `Help.lean` esto obliga a resincronizar los 77 mensajes esperados de
`#guard_msgs`, porque la ayuda que se imprime cambia.

---

## Lo que sigue fallando

Un solo caso, y no tiene arreglo léxico: **la conjunción como argumento NO
final de una aplicación**.

```
Como g y z y P concluimos que g y z ∧ P
```

Se lee `g` ⊗ `y` ⊗ `z y P`. Si `y` es un argumento intermedio, detrás viene otro
argumento, que por fuerza puede empezar un término, así que la heurística 2 no
lo ve. Distinguir `f y` (aplicación) de `f` ⊗ `y` (dos hechos) necesita tipos, y
en el momento del corte no hay tipos: el parseo termina antes de que empiece la
elaboración.

Nótese que no hace falta que haya conjunción: `Como g y z obtenemos ...` también
se parte. La regla es sobre `y` como argumento intermedio, no sobre conjunciones.

Para eso está el diagnóstico: el error lleva una nota que lo explica y, cuando
se puede, un botón [apply] que pone los paréntesis.

| familia                          | nota | botón |
|----------------------------------|------|-------|
| `Como ...` (4 formas)            | sí   | sí    |
| `Por ...` (2 formas)             | sí   | sí    |
| `Concluimos por ...`             | sí   | sí    |
| `Supongamos que ...`             | sí   | sí    |
| `Por desarrollo ... ya que ...`  | sí   | NO    |
| `Afirmación ... ya que / pues`   | sí   | NO    |

Las dos últimas llegan por expansión de macro, y después de expandir el rango de
origen ya no cubre el texto que habría que reescribir. Se puede explicar el
problema pero no arreglarlo de un clic.

Consecuencia de «profundidad 0» que conviene saber: dentro de un paréntesis la
`y` es SIEMPRE un identificador normal, nunca una conjunción. Por eso
`(A y B) y (C y D)` no funciona (`A` no es una función) y sí funciona `(g y z)`
(`g` sí lo es). El paréntesis no protege una conjunción: convierte lo de dentro
en un término corriente. Para juntar proposiciones dentro de un hecho se usa `∧`,
y para una lista de tres, la coma: `Como A, B y C ...`. Detalle en
`Exceptions.lean`, §1f.

En la práctica esto casi no se nota. El único sitio donde apetecería una `y`
anidada entre paréntesis es hablando de lógica, juntando proposiciones, y ahí lo
que se escribe en papel es `∧`, no «y». Así que la forma que Verbose pide es la
que el estudiante ya usa fuera de Lean. La `y` de Verbose es la de la prosa
(«como A y B, concluimos...»), no un conectivo lógico; el conectivo es `∧`.

Segunda limitación, de mantenimiento: `canEndTerm`, `canStartTerm` y la lista de
ligadores son listas escritas a mano. Cada notación nueva de Mathlib o de
Verbose es un fallo en potencia. No es teórico: al añadir `fun` hubo que añadir
`↦`, porque sin él `fun y ↦ y` se cortaba en el cuerpo.

---

## Verificación

* `lake build`: 1276 objetivos, sin errores.
* Los 327 ejemplos del banco compilan SIN un solo paréntesis añadido.
* Los 77 `#guard_msgs` de `Help.lean` pasan.
* Inglés y francés sin tocar: no se modifica la tabla global de tokens.
* Las sugerencias se comprobaron aplicándolas automáticamente y recompilando, no
  leyéndolas. Así se encontraron los dos fallos del párrafo de `conjFixText`.
* Comprobado que no queda ningún `sorry` silencioso: ningún fichero español
  produce el aviso `declaration uses 'sorry'`.

---

# Revisión del escáner — 17/09/2026, Iván Martínez

Cinco cambios en `Conjunction.lean`. Los cuatro primeros son fallos que el banco
de 327 ejemplos no cubría; el quinto es de coste, y de paso de correctitud.

Un aviso que conviene tener presente al leer lo que sigue: la pista de
`withConjHint` sólo se dispara cuando SÍ ha habido un corte. Si el escáner no
llega a cortar, no hay nodo `AndES` en el árbol, no hay nada que diagnosticar y
el estudiante se queda con el error pelado de Lean. Por eso los fallos «no
corta» (1 y 3) son peores que los fallos «corta mal» (2).

## 1. `|` fuera de las dos listas de caracteres

```lean
-  !c.isWhitespace && !"=<>≤≥≠+-*/^∈∉⊆∧∨→↔↦∘¬,;:(⟨[{|".contains c   -- canEndTerm
+  !c.isWhitespace && !"=<>≤≥≠+-*/^∈∉⊆∧∨→↔↦∘¬,;:(⟨[{".contains c
-  !c.isWhitespace && !"=<>≤≥≠+*/^∈∉⊆∧∨→↔↦∘,;:)⟩]}|".contains c     -- canStartTerm
+  !c.isWhitespace && !"=<>≤≥≠+*/^∈∉⊆∧∨→↔↦∘,;:)⟩]}".contains c
```

Con `|` en las listas, un hecho que acababa en barra o el siguiente que
empezaba por barra dejaban la frase entera como un solo término:

```
Como n ≥ N y |u n - l| ≤ ε concluimos que ...
  error: unexpected token '≤'; expected 'basta', 'concluimos', ...
```

Sin nota y sin botón, porque no hubo corte. Y es vocabulario básico de los
ejemplos: antes de este cambio `Verbose/Spanish` ya tenía 95 valores absolutos,
`|u n - l|` 20 veces, `|u n - x₀|` 9, `|x - x₀|` 5, `|f (u n) - f x₀|` 5. El
banco pasaba porque ninguno de ellos pone una conjunción al lado de una barra.

Quitarlas es seguro: a profundidad 0 una barra sólo puede abrir o cerrar un
valor absoluto. La del constructor de conjuntos (`{y | y = y}`) va siempre
dentro de llaves, o sea a profundidad ≥ 1, y al salir de un paréntesis `lastEnd`
ya se pone a `true` de todos modos. La de divisibilidad es otro carácter (`∣`,
U+2223) y no estaba en las listas.

## 2. Los operadores grandes también ligan variables

```lean
-def isBinderHead (c : Char) : Bool := "∀∃λΣΠ".contains c
+def isBinderHead (c : Char) : Bool := "∀∃λΣΠ∑∏⋃⋂⨆⨅⨁⨂".contains c
```

Sin ellos, el corte se hacía dentro de la cabecera, por una variable LIGADA:

```
s = ⋃ y z, {y + z} y P     antes: s = ⋃ ⊗ y z, ...     ahora: s = ⋃ y z, {y + z} ⊗ y P
```

Con un solo ligador (`⋃ y, ...`) ya se salvaba solo, por la heurística 2:
detrás de la `y` ligada viene una coma, que no puede empezar término. El fallo
sólo aparecía con dos o más.

## 3. Comentarios de bloque

Antes sólo se trataba `--`. El contenido de un `/- -/` movía `lastEnd` y la
profundidad de paréntesis, así que `Como P /- y -/ y Q` o `Como P /- ) ( -/ y Q`
se quedaban sin conjunción. Peor: una comilla suelta dentro de un comentario
mandaba `skipString` hasta el final del fichero.

Se añade `skipBlock`, con anidamiento, y se mira ANTES que las comillas. El
comentario es espacio en blanco, así que `lastEnd` se conserva al saltarlo.

## 4. La sangría se mide hasta el primer carácter de código

```lean
+def isIndentChar (c : Char) : Bool :=
+  c == ' ' || c == '\t' || c == '\r' || c == '·' || c == '.'
```

`indentAt` contaba espacios iniciales. Un foco de viñeta (`·`) no es un espacio,
así que el cuerpo de la viñeta parecía MÁS indentado que su propia línea y la
heurística 3 dejaba pasar la táctica siguiente como segundo miembro:

```
constructor
· Como x = y y P x se tiene que P y
  exact hPy                              -- se lo tragaba
```
```
error: Unknown identifier `exact`
error: No se pudo probar: ⊢ sorry ∧ sorry
```

La misma táctica sin viñeta funcionaba, que es lo que hacía difícil de ver el
fallo. Ahora `indentAt` devuelve la byte-columna del primer carácter de código,
que es la misma unidad que usa `colOf`.

(`\t` está por simetría, pero es código muerto: Lean rechaza los tabuladores.)

## 5. El escáner no sale del bloque de la táctica

`stop` es `c.endPos`, o sea el final del FICHERO. Cuando una táctica no tenía
conjunción detrás — que es el caso más común, `Como h concluimos que P` —
`findSep` recorría el resto del fichero entero. Coste cuadrático en el tamaño
del fichero:

| fichero | antes | ahora |
|---|---|---|
| 400 ejemplos sin conjunción | 31,8 s | 1,6 s |
| 100 ejemplos + 8000 líneas de comentario al final | 14,4 s | 1,6 s |

La segunda fila es el control: 8000 líneas de comentario no añaden ni un
objetivo que elaborar, y costaban 8,8 s.

No es sólo coste. Al pasarse de largo, el escáner podía cortar por una `y` de la
táctica SIGUIENTE:

```
Como h concluimos que P
exact foo y bar            -- antes cortaba aquí
```

`leavesBlock` para en la primera línea no vacía que vuelve a la sangría del
hecho o por debajo. Ninguna `y` posterior podría aceptarse ya, porque la
heurística 3 la rechazaría.

Un detalle que costó un intento fallido: `inBinder` NO se reinicia al saltar de
línea. Parece razonable hacerlo, pero una cabecera de ligadura puede partirse en
dos líneas y entonces la `y` de la segunda sigue siendo una variable ligada:

```
Como ∀ x
      y z : ℕ, x + y + z = 0 y P ...
```

Reiniciarlo cortaba justo ahí, por la `y` ligada — el mismo fallo del punto 2,
reintroducido. Y no hace falta: toda cabecera se cierra con `,`, `=>` o `↦`. Hay
un comentario en el código para que no se vuelva a añadir.

## Verificación

* `lake build`: 1276 objetivos, sin errores. `Examples.lean` compila sin tocarlo,
  y los 327 ejemplos del banco siguen sin necesitar un solo paréntesis añadido.
* Comparando el escáner viejo y el nuevo sobre unas 60 cadenas, sólo cambian 12,
  y las 12 a mejor (2 de ligadores, 5 de comentarios, 4 de barras, 1 de invadir
  la táctica siguiente). El resto sale idéntico byte a byte.
* Las sugerencias con botón [apply] salen idénticas a las de antes en todos los
  casos comprobados: listas de tres y de cuatro hechos, conjunción partida en
  dos líneas, `obtenemos`, `usando` y `Supongamos que`. Y siguen sin ofrecerse
  cuando el grupo ya está entre paréntesis.
* `Exceptions.lean` pasa de 42 a 57 ejemplos compilados, más cuatro `#guard`
  sobre `findSep`. Los `#guard` son para los operadores grandes: Verbose no
  importa esa notación, así que no se puede escribir un `example` que elabore, y
  como la regla es léxica se prueba donde vive.
