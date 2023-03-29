;;; IC: Trabajo (2017/2018)
;;; Universidad de Sevilla
;;; Departamento de Ciencias de la Computaci�n e Inteligencia Artificial
;;; M�ster Universitario en L�gica, Computaci�n e Inteligencia Artificial
;;; Resoluci�n deductiva de un Kakuro
;;;============================================================================
;;; AUTOR: Luis Cede�o Valarezo
;;;============================================================================


;;;============================================================================
;;; ORGANIZACI�N DE LAS REGLAS
;;;============================================================================
;;; Se han dividido las reglas en dos m�dulos, el m�dulo FASE-UNO agrupa
;;; las reglas m�s sencillas para resolver el Kakuro. En el m�dulo FASE-DOS
;;; est�n reglas m�s elaboradas. Adem�s se hizo necesario dividir en dos grupos
;;; pues existen reglas que deben ejecutarse en momentos diferentes para
;;; mantener la integridad de los hechos

(defmodule MAIN
   (export ?ALL))

(defmodule FASE-UNO
   (import MAIN ?ALL)
   (export ?ALL))

(defmodule FASE-DOS
   (import FASE-UNO ?ALL))


;;;============================================================================
;;; REPRESENTACI�N DEL KAKURO
;;;============================================================================

;;; Utilizaremos la siguiente plantilla para representar las celdas de
;;; Kakuro. Cada celda tiene los siguientes campos:
;;; - id: Identificador �nico de la celda
;;; - fila: N�mero de fila en la que se encuentra la celda
;;; - columna: N�mero de columna en la que se encuentra la celda
;;; - rango: Rango de valores que se pueden colocar en la celda. Inicialmente
;;;   el rango son todos los valores num�ricos de 1 a 9.
;;; De esta forma, una celda tendr� un valor asignado si y solo si dicho
;;; valor es el �nico elemento del rango.

(deftemplate MAIN::celda
  (slot id)
  (slot fila)
  (slot columna)
  (multislot rango
             (default (create$ 1 2 3 4 5 6 7 8 9))))


;;; Las siguientes variables globales sirve enumerar las restricciones del
;;; puzle y las combinaciones asociadas a cada restricci�n

(defglobal ?*restricciones* = 0)
(defglobal ?*combinaciones* = 0)


;;; La siguiente funci�n sirve para asignar de forma autom�tica y �nica
;;; identificadores a las restricciones del puzle. 

(deffunction MAIN::idRestriccion ()
  (bind ?*restricciones* (+ ?*restricciones* 1))
  ?*restricciones*)
  

;;; Utilizaremos la siguiente plantilla para almacenar las restricciones del
;;; puzle. Cada restricci�n tiene los siguientes campos:
;;; - id: Identificador �nico de la restricci�n
;;; - valor: Valor de la restricci�n
;;; - casillas: Identificadores de las casillas que se ven afectadas por la
;;;   restricci�n
;;;==========================================================================
;;; Se ha modificado la plantilla original agregando un campo:
;;; - posibles: posibles valores que se pueden asignar en la restricci�n
;;;==========================================================================

(deftemplate MAIN::restriccion
  (slot id
        (default-dynamic (idRestriccion)))
  (slot valor)
  (multislot casillas)
  (multislot posibles))


;;; La siguiente funci�n sirve para asignar de forma autom�tica y �nica
;;; identificadores a las combinaciones que se generen

(deffunction MAIN::idCombinacion ()
  (bind ?*combinaciones* (+ ?*combinaciones* 1))
  ?*combinaciones*)


;;; Se utilizar� la plantilla siguiente para almacenar las combinaciones que
;;; se puedan dar en cada restricci�n, seg�n su valor y el n�meros de celdas
;;; que son parte de dicha restricci�n. Los campos son:
;;; - id-C: Identificador de la combinaci�n
;;; - id-R: Identificador de la restricci�n a la que pertenece la combinaci�n
;;; - combinaci�n: es un campo en el que tendr� la combinaci�n de valores
;;;                que cumplan con la restricci�n (suma y n�mero de elementos)

(deftemplate MAIN::combina
  (slot id-C (default-dynamic (idCombinacion)))
  (slot id-R) 
  (multislot combinacion))


;;; La siguiente plantilla sirve para dividir las restricciones principales
;;; en subrestricciones, de ser el caso

(deftemplate MAIN::restriccionAux
   (slot id)
   (slot suma)
   (multislot celdas))

;;; Se utilizar� una plantilla para registrar los valores ya asignados a una
;;; celda as� como la restricci�n a la que pertenecen con la finalidad de
;;; eliminar la celda de la restricci�n y el valor de los posibles.

(deftemplate MAIN::valores
   (slot id-R)
   (slot valor))


;;;============================================================================
;;; ESTRATEGIAS DE RESOLUCI�N
;;;============================================================================

;;; Al inicio se agregan los hechos (procesado1) y (procesado2) que se emplean
;;; para controlar la alternancia entre los m�dulos FASE-UNO y FASE-DOS

(deffacts MAIN::inicio
   (procesado1)
   (procesado2))

;;;===========================================================================
;;; REGLAS DE CONTROL
;;;===========================================================================

;;; Pone el m�dulo FASE-UNO en ejecuci�n, si el hecho (procesado1) no existe
;;; se termina la ejecuci�n del m�dulo MAIN presentando el resultado obtenidos

(defrule MAIN::control-1
   ?h <- (procesado1)
   =>
   (retract ?h)
   (focus FASE-UNO))


;;; Una vez que se ha finalizado de ejecutar el m�dulo FASE-UNO, se pone en
;;; ejecuci�n el m�dulo FASE-DOS, en las reglas de este m�dulo se agregan
;;; los hechos (procesado1) y (procesado2) que hace que el ciclo se repita.
;;; Si en el m�dulo FASE-DOS no se activa ninguna regla el ciclo finaliza.

(defrule MAIN::control-2
    (not (procesado1))
    ?h <- (procesado2)
    =>
    (retract ?h)
    (focus FASE-DOS))


;;;============================================================================
;;; REGLAS FASE-UNO
;;;============================================================================

;;; Control de reglas f�ciles
(defrule FASE-UNO::faciles-uno
  (declare (salience -3))
  =>
  (assert (pase-1)))


;;; Cuando una celda tiene un �nico valor en su rango, el mismo es eliminado
;;; del rango de otras celdas que est�n dentro de la misma restricci�n

(defrule FASE-UNO::elimina-asignado-rango
   (celda (id ?idc1) (rango ?v))
   (restriccion (id ?idr) (casillas $? ?idc1 $?))
   (restriccion (id ?idr) (casillas $? ?idc2&~?idc1 $?))
   ?h <- (celda (id ?idc2) (rango $?ini ?v $?fin))
   =>
   (modify ?h (rango $?ini $?fin)))


;;; Elimina valores en el rango de la celda que no est�n entre los posibles
;;; valores a ser a ser asignados en las restricciones a las que pertenece
;;; dicha celda

(defrule FASE-UNO::posibles-celda
   ?h <- (celda (id ?idc) (rango $?ini ?v $?fin))
   (restriccion (id ?idr1) (casillas $? ?idc $?))
   (restriccion (id ?idr2&~?idr1) (casillas $? ?idc $?))
   (not (and (restriccion (id ?idr1) (posibles $? ?v $?))
             (restriccion (id ?idr2) (posibles $? ?v $?))))
   =>
   (modify ?h (rango $?ini $?fin)))


;;; Cuando un valor est� asignado a una celda, se toma la restricci�n a la que
;;; pertenece dicha celda y luego se eliminan las combinaciones correspondientes
;;; a dicha restricci�n en las que el valor asignado no forme parte

(defrule FASE-UNO::elimina-combinacion-sin-valor-asignado
   (celda (id ?idc) (rango ?v))
   (restriccion (id ?idr) (casillas $? ?idc $?))
   ?h1 <- (combina (id-R ?idr) (combinacion $?r))
   (test (not (member$ ?v $?r)))
   =>
   (retract ?h1))


;;; Si en una restricci�n existe un valor posible, que no forme parte de
;;; ninguna combinaci�n de dicha restricci�n, dicho valor es eliminado
;;; de la restricci�n

(defrule FASE-UNO::elimina-posibles-restriccion-sin-combinacion
   (pase-1)
   ?h <- (restriccion (id ?idr) (posibles $?ini ?v $?fin))
   (not (combina (id-R ?idr) (combinacion $? ?v $?)))
   =>
   (modify ?h (posibles $?ini $?fin)))


;;; Si en una restricci�n de dos celdas existe un valor que no posea un
;;; complementario aditivo en la otra celda, se elimina dicho valor del
;;; rango de la celda en cuesti�n

(defrule FASE-UNO::elimina-no-complementario
   (pase-1)
   (restriccion (id ?idr) (valor ?s) (casillas ? ?))
   (restriccion (id ?idr) (casillas $? ?c1 $?))
   (restriccion (id ?idr) (casillas $? ?c2&~?c1 $?))   
   ?h <- (celda (id ?c1) (rango $?i ?v $?f))
   (celda (id ?c2) (rango $?r))
   (test (not (member$ (- ?s ?v) $?r)))
   =>
   (modify ?h (rango $?i $?f)))


;;; Si en dos celdas distintas, existen dos �nicos valores posibles
;;; y ambas celdas corresponden a la misma restricci�n, se eliminan
;;; dichos valores del rango de las dem�s celdas que forman parte
;;; de dicha restricci�n

(defrule FASE-UNO::elimina-pares-asignados-rango
   (pase-1)
   ?h1 <- (celda (id ?idc1) (rango ?v1 ?v2))
   (restriccion (id ?idr) (casillas $? ?idc1 $?))
   (restriccion (id ?idr) (casillas $? ?idc2 $?))
   ?h2 <- (celda (id ?idc2) (rango ?v1 ?v2))
   (test (neq ?h1 ?h2))
   (restriccion (id ?idr) (casillas $? ?idc3 $?))
   ?h3 <- (celda (id ?idc3) (rango $?ini ?v&?v1|?v2 $?fin))
   (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
   =>
   (modify ?h3 (rango $?ini $?fin)))
   
	   
;;; Si en dos celdas distintas, existen dos �nicos valores posibles
;;; y ambas celdas corresponden a la misma restricci�n, se eliminan
;;; todas las combinaciones de la mencionada restricci�n que no
;;; contengan ambos valores entre sus n�meros

(defrule FASE-UNO::elimina-combinacion-no-pares-asignados
   (pase-1)
   ?h1 <- (celda (id ?idc1) (rango ?v1 ?v2))
   (restriccion (id ?idr) (casillas $? ?idc1 $?))
   (restriccion (id ?idr) (casillas $? ?idc2 $?))
   ?h2 <- (celda (id ?idc2) (rango ?v1 ?v2))
   (test (neq ?h1 ?h2))
   ?h3 <- (combina (id-R ?idr) (combinacion $?r))
   (test (or (not (member$ ?v1 $?r)) (not (member$ ?v2 $?r))))
   =>
   (retract ?h3))


;;; cuando una celda ya tiene un valor asignado, la misma es eliminada
;;; de las restricciones en las que aparece. Para llevar un control de
;;; esto, se agrega un hecho en el que se espec�fica el valor eliminado
;;; y la restricci�n a la que pertenece para posteriormente procesar las
;;; combinaciones de dicha restricci�n en que aparece ese valor

(defrule FASE-UNO::elimina-celdas-asignadas-restriccion
    (declare (salience -1))
    (celda (id ?idc) (rango ?v))
    ?h1 <- (restriccion (id ?idr) (valor ?s) 
                        (casillas $?i1 ?idc $?f1)
                        (posibles $?i2 ?v $?f2))
    =>
    (modify ?h1 (valor (- ?s ?v)) (casillas $?i1 $?f1) (posibles $?i2 $?f2))
    (assert (valores (id-R ?idr) (valor ?v))))


;;; Se toman los valores agregados en la regla anterior y se procede
;;; a eliminarlos de las combinaciones de la restricci�n a la que pertenecen

(defrule FASE-UNO::elimina-valor-asignado-combinaciones
    (declare (salience -2))
    (valores (id-R ?idr) (valor ?v))
    ?h <- (combina (id-R ?idr) (combinacion $?ini ?v $?fin))
    =>
    (modify ?h (combinacion $?ini $?fin)))


;;;============================================================================
;;; REGLAS FASE-DOS
;;;============================================================================

;;; Control reglas lentas 2
(defrule FASE-DOS::faciles-dos
  (declare (salience -3))
  =>
  (assert (pase-2)))

;;; Cuando existe un valor en una combinaci�n y dicho valor no se encuentra
;;; en ning�n rango de las celdas de la restricci�n a la que dicha combinaci�n
;;; corresponde, se elimina dicha combinaci�n.


(defrule FASE-DOS::elimina-combinacion-valores-no-posibles
   (pase-1)
   ?h <- (combina (id-R ?idr) (combinacion $? ?v $?))
   (forall (restriccion (id ?idr) (casillas $? ?c $?))
           (not (celda (id ?c) (rango $? ?v1&?v $?))))
   =>
   (retract ?h)
   (assert (procesado1)
	    (procesado2)))

;;; Cuando un valor est� en todas las combinaciones y es posible ubicarlo
;;; solo una celda de la restricci�n, entonces se lo fija en dicha celda

(defrule FASE-DOS::fija-unico-posible
    (pase-1)
    (pase-2)
    (combina (id-C ?cb) (id-R ?r) (combinacion $? ?v $?))
    (forall (combina (id-C ?cb1&~?cb) (id-R ?r))
            (combina (id-C ?cb1&~?cb) (id-R ?r) (combinacion $? ?v1&?v $?)))
    (restriccion (id ?r) (casillas $? ?c1 $?))
    ?h1 <- (celda (id ?c1) (rango $? ?v $?))
    (celda (id ?c1) (rango ? ? $?))
    (forall (restriccion (id ?r) (casillas $? ?c2&~?c1 $?))
            (not (celda (id ?c2&~?c1) (rango $? ?v $?))))
    =>
    (modify ?h1 (rango ?v))
    (assert (procesado1)
	    (procesado2)))


;;; si en una restricci�n de tres casillas hay una celda con un valor en su
;;; rango que no puede hacer la suma con ninguna posible combinaci�n de valores
;;; en el rango de las otras casillas, se quita ese valor del rango 

(defrule FASE-DOS::elimina-sumas-no-posibles
    (pase-1)
    (pase-2)
    (restriccion (id ?r) (valor ?s) (casillas ? ? ?))
    (restriccion (id ?r) (casillas $? ?c1 $?))
    (restriccion (id ?r) (casillas $? ?c2&~?c1 $?))
    (restriccion (id ?r) (casillas $? ?c3&~?c1&~?c2 $?))
    ?h1 <- (celda (id ?c1) (rango $?i ?v1 $?f))
    (not (and (and (celda (id ?c2) (rango $? ?v2&~?v1 $?))
         (celda (id ?c3) (rango $? ?v3&~?v1&~?v2 $?)))
	    (test (= (+ (+ ?v1 ?v2) ?v3) ?s))))
    =>
    (modify ?h1 (rango $?i $?f))
    (assert (procesado1)
	    (procesado2)))


;;; Se consideran cuatro restricciones de forma que tres de ellas tengan dos
;;; celdas �nicamente y la otra tenga tres celdas de tal forma que las celdas
;;; que las conforman se intersepten de dos en dos, quedando una de las celdas
;;; de la restricci�n de tres libre. Al sumar los valores de las restricciones
;;; en un sentido y en el otro y calcular su diferencia, se obtiene el valor
;;; de la celda libre.
;;;                       15  10
;;;                     +---+---+---+
;;;                  19 | ? | ? | X | <--- se deduce el valor 3   
;;;                     +---+---+---+
;;;                   9 | ? | ? |   
;;;                     +---+---+
;;; Las sumas de filas y columnas siempre son iguales

(defrule FASE-DOS::restricciones-cuadrado
    (pase-1)
    (pase-2)
    (restriccion (id ?r1) (valor ?s1) (casillas ? ? ?))
    (restriccion (id ?r2) (valor ?s2) (casillas ? ?))
    (restriccion (id ?r1) (casillas $? ?c1 $?))
    (restriccion (id ?r1) (casillas $? ?c2&~?c1 $?))
    (restriccion (id ?r1) (casillas $? ?c3&~?c1&~?c2 $?))
    (restriccion (id ?r2) (casillas $? ?c4 $?))
    (restriccion (id ?r2) (casillas $? ?c5&~?c4 $?))    
    ?h1 <- (restriccion (id ?r3&~?r2) (valor ?s3)
                        (casillas ?c1|?c2|?c4|?c5 ?c1|?c2|?c4|?c5))
    ?h2 <- (restriccion (id ?r4&~?r2) (valor ?s4)
                        (casillas ?c1|?c2|?c4|?c5 ?c1|?c2|?c4|?c5))
    (test (neq ?h1 ?h2))
    ?h3 <- (celda (id ?c3)(rango ? ? $?))
    =>
   (modify ?h3 (rango (- (+ ?s1 ?s2) (+ ?s3 ?s4))))
   (assert (procesado1)
	   (procesado2)))


;;; Se consideran cuatro restricciones de forma que tres de ellas tengan dos
;;; celdas �nicamente y la otra tenga cuatro celdas de tal forma que las celdas
;;; que las conforman se intercepten de dos en dos, quedando dos celdas de la
;;; restricci�n de cuatro libres. Al sumar los valores de las restricciones
;;; en un sentido y en el otro y calcular su diferencia, se obtiene el valor
;;; de la suma de las dos celdas libres, y la diferencia entre este valor y
;;; el de la restricci�n a la que pertenecen es el valor de la suma de las
;;; otras dos celdas de dicha restricci�n. Se crean entonces dos restricciones
;;; auxiliares.
;;;                       14  10
;;;                     +---+---+---+---+
;;;                  22 | ? | ? | X | Y | <--- la suma de X e Y es 10   
;;;                     +---+---+---+---+      las otras dos suman 12
;;;                  12 | ? | ? |   
;;;                     +---+---+
;;; Recordemos que las sumas de filas y columnas siempre son iguales

(defrule FASE-DOS::divide-restricciones
    (pase-1)
    (pase-2)
    (restriccion (id ?r1) (valor ?s1) (casillas ? ? ? ?))
    (restriccion (id ?r2) (valor ?s2) (casillas ? ?))
    (restriccion (id ?r1) (casillas $? ?c1 $?))
    (restriccion (id ?r1) (casillas $? ?c2&~?c1 $?))
    (restriccion (id ?r1) (casillas $? ?c3&~?c1&~?c2 $?))
    (restriccion (id ?r1) (casillas $? ?c4&~?c1&~?c2&~?c3 $?))
    (restriccion (id ?r2) (casillas $? ?c5 $?))
    (restriccion (id ?r2) (casillas $? ?c6&~?c5 $?))    
    ?h1 <- (restriccion (id ?r3&~?r2) (valor ?s3)
                        (casillas ?c1|?c2|?c5|?c6 ?c1|?c2|?c5|?c6))
    ?h2 <- (restriccion (id ?r4&~?r2) (valor ?s4)
                        (casillas ?c1|?c2|?c5|?c6 ?c1|?c2|?c5|?c6))
    (test (neq ?h1 ?h2))
    =>
    (assert (restriccionAux (id (sym-cat ?r1 "-1"))
                            (suma (- (+ ?s1 ?s2) (+ ?s3 ?s4)))
			    (celdas ?c3 ?c4))
	    (restriccionAux (id (sym-cat ?r1 "-2"))
                            (suma (- ?s1 (- (+ ?s1 ?s2) (+ ?s3 ?s4))))
			    (celdas ?c1 ?c2)))	    
    (assert (procesado1)
	    (procesado2)))


;;; si en una restricci�n auxiliar existen en dos celdas dos valores iguales
;;; y esos dos valores suman el valor de la restricci�n, entonces dichos
;;; valores se eliminan del rango de las celdas

(defrule FASE-DOS::elimina-no-posibles-aux
    (pase-1)
    (pase-2)
    (restriccionAux (suma ?s) (celdas ?c1 ?c2))
    ?h1 <- (celda (id ?c1) (rango $?i1 ?v1 $?f1))
    ?h2 <- (celda (id ?c2) (rango $?i2 ?v2&?v1 $?f2))
    (test (= (+ ?v1 ?v2) ?s))
    =>
    (modify ?h1 (rango $?i1 $?f1))
    (modify ?h2 (rango $?i2 $?f2)))


;;;============================================================================
;;; REGLAS PARA IMPRIMIR EL RESULTADO
;;;============================================================================

;;; Las siguientes reglas permiten visualizar el estado del puzle, una vez
;;; aplicadas todas las reglas que implementan las estrategias de resoluci�n.
;;; La prioridad de estas reglas es -10 para que sean las �ltimas en
;;; aplicarse.

;;; Para las casillas del tablero con un �nico valor en su rango se indica
;;; dicho valor, para las casillas del tablero en las que no se haya podido
;;; deducir el valor se indica el s�mbolo '?'. El resto de las casillas hasta
;;; completar la cuadr�cula 9x9 se dejan en blanco.

(defrule MAIN::imprime-solucion
  (declare (salience -10))
  =>
  (printout t "+---------+" crlf "|")
  (assert (imprime 1 1)))


(defrule MAIN::imprime-celda-1
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (celda (fila ?i) (columna ?j) (rango $?v))
  =>
  (retract ?h)
  (if (= (length$ $?v) 1)
      then (printout t (nth$ 1 $?v))
    else (printout t "?"))
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))


(defrule MAIN::imprime-celda-2
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (not (celda (fila ?i) (columna ?j) (rango $?v)))
  =>
  (retract ?h)
  (printout t " ")
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

;;;============================================================================
;;; FUNCIONALIDAD PARA LEER LOS PUZLES DEL FICHERO DE EJEMPLOS
;;;============================================================================

;;;============================================================================
;;; FUNCION PARA GENERAR COMBINACIONES Y VALORES POSIBLES EN RESTRICCIONES
;;;============================================================================
;;; La siguiente funci�n que genera las combinaciones posibles de acuerdo al
;;; valor de la restricci�n y la cantidad de celdas involucradas. Adem�s, de
;;; acuerdo a eso calcula los posibles valores de la restricci�n que se est�
;;; procesando. Los par�metros son:
;;;   - ?p: Aqu� se van agregando los posibles valores de la restricci�n
;;;   - ?c: Aqu� se van generando las combinaciones
;;;   - ?t: Indica el n�mero de celdas en la restricci�n
;;;   - ?v: Indica el valor de la restricci�n
;;;   - ?i: Es el valor a partir del cual se est� combinando, al inicio es uno
;;;         y de manera recursiva va aumentando hasta 9.


(deffunction MAIN::combinar (?p ?c ?t ?v ?i)
    (bind ?d (create$ 1 2 3 4 5 6 7 8 9))
    (bind ?l (length$ ?c))
    (if (= ?l ?t) then 
        (bind ?s 0)
        (bind ?j 1)
        (while (<= ?j ?l)
	    (bind ?vl (nth$ ?j ?c))
	    (bind ?s (+ ?s ?vl))
	    (bind ?j (+ 1 ?j)))
	(if (= ?s ?v) then
	    (bind ?j 1)
	    (while (<= ?j (length$ ?c))
	        (bind ?vl (nth$ ?j ?c))
	        (if (not (member$ ?vl ?p)) then
	            (bind ?p (insert$ ?p (+ 1 (length$ ?p)) (create$ ?vl))))
	        (bind ?j (+ 1 ?j)))
	    (assert (combina (id-R (+ 1 ?*restricciones*)) (combinacion ?c))))
     else
	(bind ?k ?i)
	(while (<= ?k 9)
	    (bind ?c (insert$ ?c (+ 1 (length$ ?c)) (subseq$ ?d ?k ?k)))
	    (bind ?p (combinar ?p ?c ?t ?v (+ 1 ?k)))
	    (bind ?c (delete$ ?c (length$ ?c) (length$ ?c)))
	    (bind ?k (+ 1 ?k))))
     ?p)
	    

;;; Esta funci�n crea una lista de identificadores de casillas en horizontal.

(deffunction MAIN::crea-casillas-horizontal (?f ?c ?n)
   (bind ?datos (create$))
   (loop-for-count
       (?i 0 (- ?n 1))
       (bind ?datos (insert$ ?datos ?n (eval (str-cat ?f (+ ?c ?i))))))
   ?datos)

;;; Esta funci�n construye los hechos que representan las restricciones de
;;; una l�nea horizontal del Kakuro.
;;;============================================================================
;;; Se ha modificado esta funci�n para mediante la funci�n de nombre combinar
;;; generar las combinaciones de la restricci�n en curso y determinar los
;;; posibles valores de la misma.
;;;============================================================================

(deffunction MAIN::procesa-restricciones-fila (?f $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (bind ?nc 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?c ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?nc (+ ?nc 1))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?c))
        then (bind ?x (create$))
	     (bind ?p (create$))
	     (bind ?p (combinar ?p ?x ?nc ?v 1))
	     (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-horizontal ?f ?c (- ?i ?c)))
		      (posibles ?p)))))
  TRUE)


;;; Esta funci�n crea una lista de identificadores de casillas en vertical.

(deffunction MAIN::crea-casillas-vertical (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat (+ ?f ?i) ?c)))))
  ?datos)


;;; Esta funci�n construye los hechos que representan las restricciones de
;;; una l�nea horizontal del Kakuro.
;;;============================================================================
;;; Se ha modificado esta funci�n para mediante la funci�n de nombre combinar
;;; generar las combinaciones de la restricci�n en curso y determinar los
;;; posibles valores de la misma.
;;;============================================================================

(deffunction MAIN::procesa-restricciones-columna (?c $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (bind ?nc 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?f ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?nc (+ ?nc 1))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?f))
        then (bind ?x (create$))
	     (bind ?p (create$))
	     (bind ?p (combinar ?p ?x ?nc ?v 1))
	     (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-vertical ?f ?c (- ?i ?f)))
		      (posibles ?p)))))
  TRUE)


;;; Esta funci�n construye todos los hechos que representan las restricciones
;;; de un Kakuro dado en el formato utilizado en el fichero de ejemplos.

(deffunction MAIN::procesa-restricciones-ejemplo (?datos)
  (loop-for-count
   (?i 1 9)
   (bind $?linea (create$))
   (loop-for-count
    (?j 2 10)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-fila ?i ?linea))
  (loop-for-count
   (?j 2 10)
   (bind $?linea (create$))
   (loop-for-count
    (?i 1 9)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-columna (- ?j 1) ?linea))
  TRUE)


;;; Esta funci�n localiza el Kakuro que se quiere resolver en el fichero de
;;; ejemplos.

(deffunction MAIN::lee-kakuro (?n)
  (open "ejemplos.txt" data "r")
  (loop-for-count (?i 1 (- ?n 1))
                  (readline data))
  (bind ?datos (readline data))
  (procesa-restricciones-ejemplo ?datos)
  (close data))


;;; Esta regla pregunta al usuario que n�mero de Kakuro del fichero de
;;; ejemplos se quiere resolver y genera los hechos que representan las
;;; restricciones asociadas.

(defrule MAIN::kakuro-numero
  (declare (salience 100))
  =>
  (printout t "Qu� problema quieres resolver (1-50)? : ")
  (lee-kakuro (read)))

;;; Esta regla construye las celdas que aparecen en alguna de las
;;; restricciones del Kakuro que se quiere resolver.

(defrule MAIN::crea-celdas-restricciones
  (declare (salience 100))
  (restriccion (casillas $? ?id $?))
  (not (celda (id ?id)))
  =>
  (assert (celda (id ?id) (fila (div ?id 10)) (columna (mod ?id 10)))))

;;;============================================================================
;;; FINAL
;;;============================================================================