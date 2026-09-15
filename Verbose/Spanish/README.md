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
