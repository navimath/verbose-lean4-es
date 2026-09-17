import Verbose.Spanish.All

/-!
# Excepciones de la conjunción `y` / `e`

La regla de `Verbose/Spanish/Conjunction.lean` decide léxicamente, ANTES de
llamar al parser de términos, dónde está la conjunción. Se apoya en tres
heurísticas:

1. la conjunción va precedida de algo que puede TERMINAR un término
   (`canEndTerm`), a profundidad de paréntesis 0 y fuera de una cabecera de
   ligadura (`∀ ∃ λ Σ Π ∑ ∏ ⋃ ⋂ ⨆ ⨅`, `fun`, hasta `,`, `=>` o `↦`);
2. detrás de la conjunción viene algo que puede EMPEZAR un término
   (`canStartTerm`): así `f e = 0` no se parte, porque `=` no empieza término;
3. si el segundo miembro salta de línea, tiene que ir más indentado que el
   hecho: así `se tiene que P y` no se traga la táctica siguiente.

Además, el escáner sabe qué partes del texto NO son código (cadenas,
comentarios `--` y comentarios de bloque `/- -/`, anidados incluidos) y no sale
nunca del bloque de la táctica: se detiene en la primera línea que vuelve a la
sangría del hecho o por debajo. La sangría se mide hasta el primer carácter de
código, así que el foco de viñeta (`· ...`) cuenta como sangría.

Con esto, el banco de ejemplos entero (327 ejemplos) compila sin un solo
paréntesis añadido. Lo que queda documentado aquí es lo que sigue fallando.

Los casos que fallan van COMENTADOS, porque si no el fichero no compilaría. Los
que fallan ELABORANDO, en cambio, sí se pueden ejecutar con `fail_if_success`, y
así son tests de verdad en vez de prosa: ver §1g.
-/

open Verbose.Named

setLang es
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace VerboseExcepciones

/-!
## Excepción 1: la conjunción como argumento NO final de una aplicación

Es la única que queda de las inherentes, y no tiene arreglo léxico.

Si `y` (o `e`) es un argumento intermedio, detrás viene otro argumento, que
por fuerza puede empezar un término. Las heurísticas 2 y 3 no lo ven, y el
corte se hace en la `y` equivocada.

FALLA:

    example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (h : g y z) (hP : P) :
        g y z ∧ P := by
      Como g y z y P concluimos que g y z ∧ P

    error: Function expected at g

Se lee `g` ⊗ `y` ⊗ `z y P` en vez de `g y z` ⊗ `y` ⊗ `P`. Lo mismo con un
argumento entre paréntesis (`g y (z+1) y P`) y lo mismo con `e` (`g e z y P`).

Nótese que el error es de ELABORACIÓN, no de sintaxis. Por eso SÍ se puede
diagnosticar, y es lo que hace `withConjHint` (en `Common.lean`): si la táctica
falla, había una conjunción, y además alguno de los hechos no elabora por sí
solo, entonces añade esta nota al error:

    Prueba con:
      [apply] Como (g y z) y P concluimos que g y z ∧ P

    error: La afirmación
      g no parece directamente derivable de ninguna hipótesis local por sí sola.

    Nota: se ha leído una `y` (o una `e`) como conjunción, pero entonces el
    hecho `z y P` no tiene sentido por sí solo. Si esa palabra era en realidad
    un argumento, ponlo entre paréntesis: `(P y)` en vez de `P y`.

Tres cosas a la vez:

* se NOMBRA el hecho culpable (`z y P`), que sí sabemos cuál es;
* el ejemplo de la nota es anónimo (`(P y)` en vez de `P y`), porque la
  corrección exacta no siempre se puede deducir y un ejemplo con nombres
  concretos que no son los del estudiante despista más que ayuda;
* se ofrece la corrección concreta con botón [apply], que reescribe la táctica
  entera poniendo los paréntesis. Eso sí se puede calcular: sabemos dónde
  empieza el primer hecho, dónde está la conjunción, y cuál es la palabra
  siguiente.

Las tres condiciones del disparo importan. La tercera evita el ruido: en
`Como P y Q concluimos que R`, que falla porque `R` no se sigue, los dos hechos
elaboran perfectamente y no se dice nada.

Sigue siendo un fallo: hay que poner los paréntesis. Pero ahora el estudiante
sabe por qué, y le basta con pulsar el botón.
-/

example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (h : g y z) (hP : P) :
    g y z ∧ P := by
  Como (g y z) y P concluimos que g y z ∧ P

/-!
### 1a. No hace falta que haya conjunción

Lo importante: el corte se hace por `y` como argumento NO final, HAYA O NO una
conjunción en la frase. Aquí no hay ninguna `y` de conjunción y aun así falla:

    Como g y z obtenemos k tal que k = 0

Se lee `g` ⊗ `y` ⊗ `z`. Así que `g y z` no se puede escribir sin paréntesis en
ninguna táctica `Como`, aunque no haya conjunción por ningún lado.

### 1b. Cuando ni siquiera parsea, no hay pista posible

Si el corte rompe la sintaxis de la táctica entera, el elaborador no llega a
ejecutarse y no se puede decir nada. Con una lista de tres (`A, B y C`):

    Como g y z, P y Q concluimos que g y z ∧ P

    error: unexpected token ','; expected 'basta', 'concluimos', 'obtenemos',
           'se' o 'tenemos'

El corte deja `Como g ⊗ y ⊗ z` y la coma siguiente ya no encaja. La versión con
paréntesis, `Como (g y z), P y Q ...`, sí parsea.

Aquí la pista NO aparece, y es lo correcto: el árbol de sintaxis está
incompleto, y una sugerencia calculada sobre él saldría truncada. `conjFixText`
comprueba que la sugerencia vuelva a parsear como táctica antes de ofrecerla;
si no, no ofrece nada. Sin esa comprobación, pulsar [apply] BORRARÍA el resto
de la línea del estudiante.
-/

/-!
### 1c. Banco de casos: qué produce el botón [apply]

Cada ejemplo de abajo es el resultado de pulsar [apply] sobre el caso que
aparece comentado encima. Todos compilan, así que sirven de test de regresión:
si alguna vez la sugerencia deja de ser correcta, este fichero deja de compilar.

Se comprobó aplicando las sugerencias automáticamente y recompilando, no
leyéndolas por encima. Así se encontraron dos fallos que a ojo no se veían:
la sugerencia envolvía hasta la palabra siguiente en vez de hasta la
conjunción siguiente (`(g y z) w` en vez de `(g y z w)`), y en los casos que
no parseaban salía truncada.
-/

-- 2 argumentos     ·  estudiante: Como g y z y P concluimos que g y z ∧ P
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (h : g y z) (hP : P) :
    g y z ∧ P := by
  Como (g y z) y P concluimos que g y z ∧ P

-- 3 argumentos     ·  estudiante: Como g y z w y P concluimos que g y z w ∧ P
example (g : ℕ → ℕ → ℕ → Prop) (y z w : ℕ) (P : Prop) (h : g y z w) (hP : P) :
    g y z w ∧ P := by
  Como (g y z w) y P concluimos que g y z w ∧ P

-- argumento entre paréntesis  ·  estudiante: Como g y (z+1) y P concluimos ...
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (h : g y (z+1)) (hP : P) :
    g y (z+1) ∧ P := by
  Como (g y (z+1)) y P concluimos que g y (z+1) ∧ P

-- con `e`          ·  estudiante: Como g e z y P concluimos que g e z ∧ P
example (g : ℕ → ℕ → Prop) (e z : ℕ) (P : Prop) (h : g e z) (hP : P) :
    g e z ∧ P := by
  Como (g e z) y P concluimos que g e z ∧ P

-- `y` como argumento FINAL, seguida de la conjunción de verdad
-- estudiante: Como g x y y P concluimos que g x y ∧ P
example (g : ℕ → ℕ → Prop) (x y : ℕ) (P : Prop) (h : g x y) (hP : P) :
    g x y ∧ P := by
  Como (g x y) y P concluimos que g x y ∧ P

-- lo mismo con `e` ·  estudiante: Como g x e y P concluimos que g x e ∧ P
example (g : ℕ → ℕ → Prop) (x e : ℕ) (P : Prop) (h : g x e) (hP : P) :
    g x e ∧ P := by
  Como (g x e) y P concluimos que g x e ∧ P

-- argumento numérico  ·  estudiante: Como g y 3 y P concluimos que g y 3 ∧ P
example (g : ℕ → ℕ → Prop) (y : ℕ) (P : Prop) (h : g y 3) (hP : P) :
    g y 3 ∧ P := by
  Como (g y 3) y P concluimos que g y 3 ∧ P

-- aplicación dentro de una igualdad
-- estudiante: Como f y z = 0 y P concluimos que f y z = 0 ∧ P
example (f : ℕ → ℕ → ℕ) (y z : ℕ) (P : Prop) (h : f y z = 0) (hP : P) :
    f y z = 0 ∧ P := by
  Como (f y z = 0) y P concluimos que f y z = 0 ∧ P

-- primer hecho compuesto  ·  estudiante: Como R ∧ g y z y P concluimos ...
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P R : Prop) (h : R ∧ g y z) (hP : P) :
    (R ∧ g y z) ∧ P := by
  Como (R ∧ g y z) y P concluimos que (R ∧ g y z) ∧ P

-- `y` también dentro del argumento  ·  estudiante: Como g y (f y) y P ...
example (g : ℕ → ℕ → Prop) (f : ℕ → ℕ) (y : ℕ) (P : Prop) (h : g y (f y)) (hP : P) :
    g y (f y) ∧ P := by
  Como (g y (f y)) y P concluimos que g y (f y) ∧ P

/-!
### 1d. La pista funciona en TODAS las tácticas, no sólo en `Como`

`withConjHint` sólo necesita la sintaxis: saca del árbol la primera conjunción y
el hermano que la precede, así que no necesita saber cómo se llama el nodo de
hechos de cada táctica. Eso permite envolver cualquiera.

Está puesto en `Como ... concluimos/obtenemos/se tiene que/basta probar/elegimos`,
`Por ... tenemos/obtenemos/podemos elegir/basta probar`, `Concluimos por ...`,
`Combinamos ...` y `Supongamos que ...`.

Comprobado que sale la sugerencia correcta en las siete familias:

    Como (g y z) y P concluimos que g y z ∧ P
    Supongamos que (g y z) y Q
    Por h basta probar que (g y z) y R
    Concluimos por h aplicado a (g y z) y 1
    Por h aplicado a (g y z) y 1 tenemos hh : P (g y z) 1
    Como (g y z) y P obtenemos k tal que k = 0
    Como (g y z) y P se tiene que (g y z) ∧ P

Hubo que vigilar DOS formas de fallar. Casi todas las tácticas LANZAN una
excepción, pero algunas (`Por ... aplicado a ... tenemos ...`) terminan «bien» y
sólo REGISTRAN el error por dentro. Con un `try/catch` a secas esas se quedaban
sin pista.
-/

-- otras tácticas, no sólo `concluimos que`
-- estudiante: Como g y z y P se tiene que (g y z) ∧ P
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (hg : g y z) (hP : P) : True := by
  Como (g y z) y P se tiene que (g y z) ∧ P
  trivial

-- estudiante: Como g y z ↔ Q basta probar que Q
example (g : ℕ → ℕ → Prop) (y z : ℕ) (Q : Prop) (h : (g y z) ↔ Q) (hq : Q) : g y z := by
  Como ((g y z) ↔ Q) basta probar que Q
  exact hq

/-!
En `obtenemos` la sugerencia también sale bien
(`Como (g y z) obtenemos k tal que k = 0`), pero no se deja aquí un ejemplo
compilado porque montar un existencial que dependa de `g y z` a profundidad 0
obliga a un enunciado artificial que ya no ilustra nada.

Los dos casos en los que NO se ofrece sugerencia, y es lo correcto:

* `Como P y g y z concluimos que P ∧ g y z` funciona tal cual, sin corte
  erróneo: la `y` va después de `P`, y detrás viene `g`. No hay nada que
  arreglar y no se dice nada.
* `Como g y z, P y Q concluimos que ...` ni siquiera parsea (§1b), así que no
  hay árbol sobre el que calcular nada.
-/

-- otras familias de táctica, con el corte ya arreglado
-- estudiante: Supongamos que g y z y Q
example (g : ℕ → ℕ → Prop) (y z : ℕ) (Q : Prop) : g y z → Q → True := by
  Supongamos que (g y z) y Q
  trivial

example (g : ℕ → ℕ → Prop) (y z : ℕ) (Q : Prop) : Q → (g y z) → True := by
  Supongamos que Q y g y z
  trivial

-- estudiante: Concluimos por h aplicado a g y z y 1
example (P : ℕ → ℕ → Prop) (g : ℕ → ℕ → ℕ) (y z : ℕ) (h : ∀ a b, P a b) :
    P (g y z) 1 := by
  Concluimos por h aplicado a (g y z) y 1

-- estudiante: Por h aplicado a g y z y 1 tenemos hh : P (g y z) 1
example (P : ℕ → ℕ → Prop) (g : ℕ → ℕ → ℕ) (y z : ℕ) (h : ∀ a b, P a b) : True := by
  Por h aplicado a (g y z) y 1 tenemos hh : P (g y z) 1
  trivial

/-!
### 1e. Ejemplos límite, familia por familia

Uno por cada familia de táctica, todos con el mismo caso límite: `g y z`, donde
la `y` es un argumento intermedio. Arriba en comentario va lo que escribiría el
estudiante; abajo, compilado, lo que devuelve la corrección.

Cobertura de la pista, medida:

| familia                          | nota | botón [apply] |
|----------------------------------|------|---------------|
| `Como ... concluimos que`        | sí   | sí            |
| `Como ... se tiene que`          | sí   | sí            |
| `Como ... obtenemos`             | sí   | sí            |
| `Como ... basta probar que`      | sí   | sí            |
| `Por ... tenemos`                | sí   | sí            |
| `Por ... basta probar que`       | sí   | sí            |
| `Concluimos por ...`             | sí   | sí            |
| `Supongamos que ...`             | sí   | sí            |
| `Por desarrollo ... ya que ...`  | sí   | NO            |
| `Afirmación ... ya que ...`      | sí   | NO            |

Las dos últimas son el límite de la herramienta: `Afirmación ... ya que ...` es
una MACRO que se expande a `Como ... concluimos que ...`, y `Por desarrollo ...
ya que ...` se expande a `comoCalcTac`. Tras la expansión, el rango de origen ya
no cubre el texto que habría que reescribir, así que se puede explicar el
problema pero no ofrecer el arreglo de un clic. El estudiante tiene que poner
los paréntesis a mano.
-/

-- Como ... concluimos que        (nota sí, botón sí)
-- estudiante: Como g y z y P concluimos que g y z ∧ P
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (h : g y z) (hP : P) :
    g y z ∧ P := by
  Como (g y z) y P concluimos que g y z ∧ P

-- Como ... se tiene que          (nota sí, botón sí)
-- estudiante: Como g y z y P se tiene que (g y z) ∧ P
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (hg : g y z) (hP : P) : True := by
  Como (g y z) y P se tiene que (g y z) ∧ P
  trivial

-- Como ... basta probar que      (nota sí, botón sí)
-- estudiante: Como g y z ↔ Q basta probar que Q
example (g : ℕ → ℕ → Prop) (y z : ℕ) (Q : Prop) (h : (g y z) ↔ Q) (hq : Q) :
    g y z := by
  Como ((g y z) ↔ Q) basta probar que Q
  exact hq

-- Supongamos que ...             (nota sí, botón sí)
-- estudiante: Supongamos que g y z y Q
example (g : ℕ → ℕ → Prop) (y z : ℕ) (Q : Prop) : g y z → Q → True := by
  Supongamos que (g y z) y Q
  trivial

-- Por ... tenemos                (nota sí, botón sí)
-- estudiante: Por h aplicado a g y z y 1 tenemos hh : P (g y z) 1
example (P : ℕ → ℕ → Prop) (g : ℕ → ℕ → ℕ) (y z : ℕ) (h : ∀ a b, P a b) : True := by
  Por h aplicado a (g y z) y 1 tenemos hh : P (g y z) 1
  trivial

-- Por ... basta probar que       (nota sí, botón sí)
-- estudiante: Por h basta probar que g y z y R
example (g : ℕ → ℕ → Prop) (y z : ℕ) (Q R : Prop) (h : g y z → R → Q)
    (hg : g y z) (hr : R) : Q := by
  Por h basta probar que (g y z) y R
  exact hg
  exact hr

-- Concluimos por ...             (nota sí, botón sí)
-- estudiante: Concluimos por h aplicado a g y z y 1
example (P : ℕ → ℕ → Prop) (g : ℕ → ℕ → ℕ) (y z : ℕ) (h : ∀ a b, P a b) :
    P (g y z) 1 := by
  Concluimos por h aplicado a (g y z) y 1

-- Por desarrollo ... ya que ...   (nota sí, botón no)
-- estudiante: Por desarrollo a ≤ f y z ya que a ≤ f y z
--                          _ ≤ b     ya que f y z ≤ b
example (f : ℕ → ℕ → ℕ) (y z a b : ℕ) (h1 : a ≤ f y z) (h2 : f y z ≤ b) : a ≤ b := by
  Por desarrollo a ≤ f y z ya que (a ≤ f y z)
    _ ≤ b ya que (f y z ≤ b)

-- Afirmación ... ya que ...       (nota sí, botón no)
-- estudiante: Afirmación H : (g y z) ∧ P ya que g y z y P
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (h : g y z) (hP : P) : True := by
  Afirmación H : (g y z) ∧ P ya que (g y z) y P
  trivial

-- Afirmación ... pues ...         (se apoya en `Concluimos por`)
-- estudiante: Afirmación H : P (g y z) 1 pues h aplicado a g y z y 1
example (P : ℕ → ℕ → Prop) (g : ℕ → ℕ → ℕ) (y z : ℕ) (h : ∀ a b, P a b) : True := by
  Afirmación H : P (g y z) 1 pues h aplicado a (g y z) y 1
  trivial

/-!
### 1f. Conjunciones anidadas y encadenadas

«A profundidad de paréntesis 0» quiere decir: fuera de todo paréntesis. El
escáner lleva la cuenta de `( ⟨ [ {` y sus cierres, y sólo toma `y` por
conjunción cuando la cuenta es cero. Dentro de paréntesis la `y` se deja en paz,
y eso NO es un descuido: es justo lo que protege `∀ (y : ℕ)`, `{y | y = y}` y
`g (f y)`.

Consecuencia: una conjunción DENTRO de paréntesis no se reconoce.

FALLA:

    Como (A y B) y (C y D) concluimos que (A ∧ B) ∧ (C ∧ D)

    error: Function expected at A, but this term has type Prop

La `y` de fuera sí es conjunción; las de dentro están a profundidad 1, así que
Lean lee `A y B` como una aplicación.

Tampoco encadena en plano, porque la lista española se escribe «A, B y C»:

    Como A y B y C concluimos que A ∧ B ∧ C

    error: Function expected at B, but this term has type Prop

En rigor no es una excepción de la regla, sino de cómo son los hechos en
Verbose: son una lista PLANA, y un grupo entre paréntesis tiene que ser un
TÉRMINO. No hay conjunciones anidadas que reconocer.

Y esto es lo mismo que hace funcionar a `(g y z)`, que es la corrección que
propone el botón [apply]. Dentro de un paréntesis la `y` es SIEMPRE un
identificador normal, nunca una conjunción. Lo que cambia es si el término que
resulta tiene sentido:

* `(g y z)` con `g : ℕ → ℕ → Prop` es la aplicación `g` a `y` y a `z`. Tiene
  sentido, y es justo lo que el estudiante quería decir.
* `(A y B)` con `A : Prop` sería aplicar `A` a dos argumentos. `A` no es una
  función, así que no tiene sentido.

O sea: el paréntesis no «protege una conjunción», sino que convierte lo de
dentro en un término corriente. Que eso sea correcto o no depende de lo que
haya dentro.

Las dos formas correctas van compiladas abajo: `∧` dentro del paréntesis, o la
lista con coma.

Aquí no sale pista, y es lo correcto: el arreglo no es poner paréntesis (ya los
hay), sino cambiar `y` por `∧` o meter una coma. `textElaborates` lo descarta
solo, porque `(A y B)` no elabora.
-/

-- conjunción de proposiciones dentro de un hecho: `∧`, no `y`
example (A B C D : Prop) (hA : A) (hB : B) (hC : C) (hD : D) :
    (A ∧ B) ∧ (C ∧ D) := by
  Como (A ∧ B) y (C ∧ D) concluimos que (A ∧ B) ∧ (C ∧ D)

-- tres hechos: lista española con coma
example (A B C : Prop) (hA : A) (hB : B) (hC : C) : A ∧ B ∧ C := by
  Como A, B y C concluimos que A ∧ B ∧ C

/-!
### 1g. Los fallos de la Excepción 1, como tests ejecutables

Arriba, cada caso que falla va en un comentario, porque un fichero con un error
no compila. Pero eso sólo hace falta cuando el fallo es de SINTAXIS. Los de la
Excepción 1 son de ELABORACIÓN —la táctica parsea, y da error al elaborar—, así
que `fail_if_success` los ejecuta de verdad: la táctica falla, el combinador lo
da por bueno, y el objetivo se cierra después a mano, con Lean pelado, que aquí
es lo que toca: lo que se está probando es el fallo, no la prueba.

Así el error deja de ser una descripción y pasa a ser un test. Si algún día
`Como g y z y P ...` empezara a funcionar —porque alguien encontrara la manera
de distinguir `f y` de `f` ⊗ `y` sin tipos—, estos ejemplos dejarían de
compilar y habría que venir aquí a quitarlos. Es la única forma de que la
documentación de un fallo no se quede obsoleta en silencio.

Lo que NO se puede escribir así es el §1b: allí el corte rompe la sintaxis de la
táctica entera, el parser se detiene y dentro del `fail_if_success` no llega a
ejecutarse nada. Mismo motivo por el que allí tampoco hay pista, y por el que la
Excepción 2 tampoco se puede testear.
-/

-- Como ... concluimos que
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (h : g y z) (hP : P) :
    g y z ∧ P := by
  fail_if_success (Como g y z y P concluimos que g y z ∧ P)
  exact ⟨h, hP⟩

-- lo mismo con `e` (§1)
example (g : ℕ → ℕ → Prop) (e z : ℕ) (P : Prop) (h : g e z) (hP : P) :
    g e z ∧ P := by
  fail_if_success (Como g e z y P concluimos que g e z ∧ P)
  exact ⟨h, hP⟩

-- §1a: no hace falta que haya conjunción para que se parta
example (g : ℕ → ℕ → Prop) (y z : ℕ) (h : g y z)
    (hex : g y z → ∃ k : ℕ, k = 0) : True := by
  fail_if_success (Como g y z obtenemos k tal que k = 0)
  trivial

-- Como ... se tiene que
example (g : ℕ → ℕ → Prop) (y z : ℕ) (P : Prop) (hg : g y z) (hP : P) : True := by
  fail_if_success (Como g y z y P se tiene que (g y z) ∧ P)
  trivial

-- Supongamos que ...
example (g : ℕ → ℕ → Prop) (y z : ℕ) (Q : Prop) : g y z → Q → True := by
  fail_if_success (Supongamos que g y z y Q)
  intro _ _
  trivial

-- Concluimos por ... aplicado a ...
example (P : ℕ → ℕ → Prop) (g : ℕ → ℕ → ℕ) (y z : ℕ) (h : ∀ a b, P a b) :
    P (g y z) 1 := by
  fail_if_success (Concluimos por h aplicado a g y z y 1)
  exact h _ _

/-!
### 1h. El texto de la sugerencia puede salir cortado (cosmético, SIN ARREGLAR)

`conjFixText` compone la sugerencia a partir del rango del NODO de táctica que
el parser llegó a construir. En `Supongamos que g y z, Q y R` ese nodo acaba en
`z`, así que la sugerencia se imprime sin la cola y parece que va a BORRAR el
`, Q y R`. No lo borra: `addSuggestion` sustituye ese mismo rango, y la cola se
queda donde estaba (`Supongamos que (g y z), Q y R`, que compila). Sólo engaña a
quien LEE la nota en vez de pulsar el botón.

Va COMENTADO porque `#guard_msgs` sólo captura los mensajes de SU comando, y la
cola sobrante produce además un `unexpected token ','; expected command` de
nivel de COMANDO que se queda fuera y tumbaría el fichero igual. Los mensajes
son los de la ejecución real; ojo, la línea del `info:` lleva un espacio final.

    /--
    info: Prueba con:
      [apply] Supongamos que (g y z)
    ---
    error: El término
      g
     no es igual por definición a
      g y z

    Nota: se ha leído una `y` (o una `e`) como conjunción, pero `g y z` sí tiene
    sentido como una sola expresión. Si esa palabra era en realidad un argumento,
    ponlo entre paréntesis: `(P y)` en vez de `P y`.
    -/
    #guard_msgs in
    example (g : ℕ → ℕ → Prop) (y z : ℕ) (Q R : Prop) : g y z → Q → R → True := by
      Supongamos que g y z, Q y R
      trivial
-/

/-!
## Excepción 2: las listas de caracteres están escritas a mano

`canEndTerm`, `canStartTerm` e `isBinderHead` son aproximaciones manuales de lo
que el parser de Lean sabe de verdad. Cada notación nueva de Mathlib o de
Verbose es un fallo en potencia.

No es teórico: al añadir `fun` hubo que añadir también `↦`, porque sin él
`fun y ↦ y` se cortaba en el cuerpo. Y `λ` parecía funcionar cuando en realidad
no lo hacía, por un motivo distinto (nadie cerraba la ligadura).

Falla de dos maneras, y no son igual de graves:

* si a `isBinderHead` le FALTA un ligador, el corte se hace dentro de la
  cabecera, por una variable LIGADA. Es lo que pasaba con los operadores
  grandes: `⋃ y z, ...` se partía por la `y` ligada. Con un solo ligador
  (`⋃ y, ...`) se salvaba solo, por la heurística 2: detrás de la `y` viene una
  coma, que no empieza término.
* si a las otras dos listas les SOBRA un carácter, no se reconoce la conjunción
  y no se parte nada. Es lo que pasaba con `|`: un hecho que acababa en barra
  (`ε ≥ |u n - l| y ...`) o el siguiente que empezaba por barra
  (`... y |u n - l| ≤ ε`) dejaban la frase entera como un solo término.

El segundo caso es el peor de los dos, y conviene tenerlo presente al tocar
estas listas: la pista de `withConjHint` sólo se dispara cuando SÍ ha habido un
corte. Si el corte no llega a hacerse no hay nodo `AndES` en el árbol, no hay
nada que diagnosticar, y el estudiante se queda con el error pelado de Lean.

El síntoma siempre es un error confuso, nunca un aviso claro.

### Por qué esta excepción no se puede escribir como test

Los dos ejemplos de arriba ya están arreglados (`⋃` está en la lista, `|` ya no
está en las otras dos), así que hoy compilan: no hay nada que atrapar.

Pero aunque se reprodujeran con otra notación —y se reproducen: `∫ y z, ...`,
`⨍ y z, ...`, `∐ y z, ...` siguen partiéndose por la variable ligada, sólo que
Verbose no importa esa notación— `fail_if_success` tampoco valdría. Cortar
dentro de una cabecera de ligadura deja un fragmento que ni siquiera parsea:

    Como ⋀ y z : ℕ, y = z y P concluimos que ...

    error: unexpected end of input; expected '(', '_' o identificador

y `fail_if_success` es un combinador de TÁCTICAS: sólo ve los fallos de
ELABORACIÓN. Cuando el parser se detiene, dentro del `fail_if_success` no llega
a ejecutarse nada y el fichero entero deja de compilar. Es el mismo motivo por
el que el §1b tampoco lleva pista.

La Excepción 1 sí falla elaborando, y por eso allí sí se puede: ver §1g.
-/

/-!
## Lo que SÍ funciona

Tests de regresión.
-/

-- aplicación con la conjunción como argumento FINAL (heurística 2)
example (f : ℕ → ℕ) (e : ℕ) (P : Prop) (h : f e = 0) (hP : P) : f e = 0 ∧ P := by
  Como f e = 0 y P concluimos que f e = 0 ∧ P

-- aplicación después de un paréntesis de cierre
example (f g : ℕ → ℕ) (y : ℕ) (P : Prop) (h : (f ∘ g) y = y) (hP : P) :
    (f ∘ g) y = y ∧ P := by
  Como (f ∘ g) y = y y P concluimos que ((f ∘ g) y = y) ∧ P

-- la táctica siguiente, a la misma indentación, no se engulle (heurística 3)
example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Como x = y y P x se tiene que P y
  exact hPy

-- pero una conjunción sí puede seguir en la línea siguiente si va indentada
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P y
    Q concluimos que P ∧ Q

-- funciones anónimas: `fun` abre la ligadura, `=>` y `↦` la cierran
example (f : ℕ → ℕ) (P : Prop) (h : f = fun y => y) (hP : P) :
    (f = fun y => y) ∧ P := by
  Como f = fun y => y y P concluimos que (f = fun y => y) ∧ P

example (f : ℕ → ℕ) (P : Prop) (h : f = λ y => y) (hP : P) :
    (f = λ y => y) ∧ P := by
  Como f = λ y => y y P concluimos que (f = λ y => y) ∧ P

example (f : ℕ → ℕ) (P : Prop) (h : f = fun y ↦ y) (hP : P) :
    (f = fun y ↦ y) ∧ P := by
  Como f = fun y ↦ y y P concluimos que (f = fun y ↦ y) ∧ P

-- ligadura `∀ y`
example (P : Prop) (h : ∀ y : ℕ, y = y) (hP : P) : (∀ y : ℕ, y = y) ∧ P := by
  Como ∀ y : ℕ, y = y y P concluimos que (∀ y : ℕ, y = y) ∧ P

-- llaves: la profundidad de paréntesis protege la `y` ligada
example (s : Set ℕ) (P : Prop) (h : s = {y | y = y}) (hP : P) :
    s = {y | y = y} ∧ P := by
  Como s = {y | y = y} y P concluimos que s = {y | y = y} ∧ P

-- `y` como primer término de un hecho (aquí es una función)
example (y : ℕ → ℕ) (x : ℕ) (P : Prop) (h : y x = 0) (hP : P) : y x = 0 ∧ P := by
  Como y x = 0 y P concluimos que y x = 0 ∧ P

-- subíndices: `y₀` es otra palabra
example (y₀ : ℕ) (P : Prop) (h : y₀ = 0) (hP : P) : y₀ = 0 ∧ P := by
  Como y₀ = 0 y P concluimos que y₀ = 0 ∧ P

-- la palabra `y` dentro de una cadena no cuenta
example (s : String) (P : Prop) (h : s = "esto y aquello") (hP : P) :
    s = "esto y aquello" ∧ P := by
  Como s = "esto y aquello" y P concluimos que s = "esto y aquello" ∧ P

/-!
### Valor absoluto

A profundidad 0 una barra sólo puede abrir o cerrar un valor absoluto: la del
constructor de conjuntos (`{y | y = y}`) va siempre dentro de llaves, o sea a
profundidad ≥ 1. Así que `|` no estorba al corte por ninguno de los dos lados.

Importa más de lo que parece: `|u n - l|` es el vocabulario básico de los
ejemplos de análisis, y aparece a los dos lados de la conjunción.
-/

-- la barra CIERRA el primer hecho
example (u : ℕ → ℝ) (l ε : ℝ) (n N : ℕ) (hu : ε ≥ |u n - l|) (hn : n ≥ N) :
    ε ≥ |u n - l| ∧ n ≥ N := by
  Como ε ≥ |u n - l| y n ≥ N concluimos que ε ≥ |u n - l| ∧ n ≥ N

-- la barra ABRE el segundo
example (u : ℕ → ℝ) (l ε : ℝ) (n N : ℕ) (hn : n ≥ N) (hu : |u n - l| ≤ ε) :
    n ≥ N ∧ |u n - l| ≤ ε := by
  Como n ≥ N y |u n - l| ≤ ε concluimos que n ≥ N ∧ |u n - l| ≤ ε

-- y en una lista de tres
example (u : ℕ → ℝ) (l ε : ℝ) (n N : ℕ) (hn : n ≥ N) (hu : |u n - l| ≤ ε)
    (he : ε > 0) : n ≥ N ∧ |u n - l| ≤ ε ∧ ε > 0 := by
  Como n ≥ N, |u n - l| ≤ ε y ε > 0 concluimos que n ≥ N ∧ |u n - l| ≤ ε ∧ ε > 0

example (u : ℕ → ℝ) (l ε : ℝ) (n : ℕ) : |u n - l| ≤ ε → ε > 0 → True := by
  Supongamos que |u n - l| ≤ ε y ε > 0
  trivial

-- la barra del constructor de conjuntos, a profundidad 1, tampoco estorba
example (s : Set ℕ) (P : Prop) (hP : P) (h : s = {y | y = y}) :
    P ∧ s = {y | y = y} := by
  Como P y s = {y | y = y} concluimos que P ∧ s = {y | y = y}

/-!
### Comentarios

Un comentario es espacio en blanco para el escáner: no cambia el `lastEnd` ni
la profundidad de paréntesis. Los de bloque se saltan enteros, con anidamiento,
y se miran ANTES que las comillas, para que una comilla suelta dentro de un
comentario no se lea como principio de cadena.
-/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P /- esto y aquello -/ y Q concluimos que P ∧ Q

-- el comentario es justo la palabra `y`
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P /- y -/ y Q concluimos que P ∧ Q

-- paréntesis descuadrados dentro del comentario
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P /- ) ( -/ y Q concluimos que P ∧ Q

-- una comilla suelta
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P /- una " suelta -/ y Q concluimos que P ∧ Q

-- comentarios anidados
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P /- (a /- anidado -/ b -/ y Q concluimos que P ∧ Q

-- comentario de línea entre la conjunción y el segundo miembro
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P y -- nota y tal
    Q concluimos que P ∧ Q

/--
### Big operators are also binders

`∑ ∏ ⋃ ⋂ ⨆ ⨅` abren cabecera de ligadura igual que `∀`.

Verbose no importa esa notación, así que aquí no se puede escribir un `example`
que elabore. Como la regla es puramente léxica, se prueba donde vive: sobre
`findSep`, con `⊗` marcando el punto de corte.

/-- Dónde corta el escáner, con `⊗` en el punto de corte. -/
private def corte (s : String) : String :=
  match Verbose.Spanish.findSep s ⟨0⟩ s.rawEndPos with
  | none   => s
  | some p => String.Pos.Raw.extract s ⟨0⟩ p ++ "⊗ " ++ String.Pos.Raw.extract s p s.rawEndPos

#guard corte "s = ⋃ y z, {y + z} y P" == "s = ⋃ y z, {y + z} ⊗ y P"
#guard corte "s = ⋂ y z, {y * z} y P" == "s = ⋂ y z, {y * z} ⊗ y P"
#guard corte "n = ∑ y z, (y + z) y P" == "n = ∑ y z, (y + z) ⊗ y P"

-- con un solo ligador ya se salvaba por la heurística 2: detrás de la `y`
-- ligada viene una coma, que no puede empezar término
#guard corte "s = ⋃ y, {y} y P"       == "s = ⋃ y, {y} ⊗ y P"
-/

example : 1=1 := rfl

/-!
### Sangría, viñetas y final del bloque

La sangría se mide hasta el primer carácter de CÓDIGO de la línea, así que el
foco de viñeta (`·`) cuenta como sangría. Si sólo se contaran los espacios, el
cuerpo de la viñeta parecería más indentado que su propia línea y la táctica
siguiente entraría como segundo miembro de la conjunción.

Y el escáner no sale del bloque de la táctica: en cuanto una línea vuelve a la
sangría del hecho o por debajo, deja de buscar. No es sólo cuestión de coste
(sin ese límite el escáner recorría el fichero ENTERO por cada hecho): una `y`
de la táctica siguiente no puede ser la conjunción de ésta.
-/

-- dentro de una viñeta, la táctica siguiente no se engulle
example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y ∧ True := by
  constructor
  · Como x = y y P x se tiene que P y
    exact hPy
  · trivial

-- ni con viñetas anidadas
example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : (P y ∧ True) ∧ True := by
  constructor
  · constructor
    · Como x = y y P x se tiene que P y
      exact hPy
    · trivial
  · trivial

-- pero el segundo miembro sí sigue en la línea siguiente si va más indentado
example (P Q : Prop) (hP : P) (hQ : Q) : (P ∧ Q) ∧ True := by
  constructor
  · Como P y
      Q concluimos que P ∧ Q
  · trivial

-- una línea en blanco por medio no es salir del bloque
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P y

    Q concluimos que P ∧ Q

end VerboseExcepciones
