/* -------------------------------------------------------------------------------
Este modelo de programación lineal se subdivide en dos secciones, porque se trata de la 
unión de dos problemas de programación lineal independientes. El código está estructurado 
de la siguiente manera: : Declaración de Sets, parámetros y variables, asignación de la 
función objetivo y finalmente la definición de las restricciones del modelo. 
Además, dentro de cada una de esas categorías, están ordenados por el tipo de 
problema que optimizan. Los elementos pertenecientes al primer problema irán 
por encima de los del segundo problema. 
---------------------------------------------------------------------------------- */


/*Sets del primer problema. */
/*Set que contiene todos los trabajadores del modelo a tener en cuenta*/
set TRABAJADORES;	

/*Set que contiene todas las tareas del modelo a tener en cuenta*/
set TAREAS;

/*Sets del segundo problema */
/*Set que contiene todos los vehículos disponibles en el problema */
set VEHICULOS;	

/*Sets contenidos dentro del set VEHICULOS agrupando a los tres 
camiones de mayor y menor consumo. ACONSUMO: Alto consumo, BCONSUMO:
Bajo consumo */
set ACONSUMO within VEHICULOS;
set BCONSUMO within VEHICULOS;

/*Set que contiene todos los destinos posibles en el problema */
set DESTINOS;

/*Sets contenidos dentro del set DESTINOS agrupando los destinos 
de recogida(DESTINO_1) y el destino de entrega(DESTINO_2) */
set DESTINOS_1 within DESTINOS;
set DESTINOS_2 within DESTINOS;


/*Parámetros del primer problema*/
/*Parámetro que alamcena el coste por hora de cada trabajador
en una tarea*/
param remuneracion{i in TRABAJADORES, j in TAREAS};

/*Parámetro que alamcena el tiempo máximo al que están dispuestos
los trabajadores a trabajar en cada tarea*/
param tiempo_max{i in TRABAJADORES, j in TAREAS};

/*Parámetro que almacena el número de horas que hay que cumplir 
obligatoriamente en cada tarea*/
param horas_por_tarea{j in TAREAS};

/*Parámetro que almacena el número de horas máxima por jornada de trabajo*/
param max_horas;

/*Parámetros del segundo problema*/
/*Almacena las preferencia de los conductores por destino de recogida*/
param preferencias{i in VEHICULOS, j in DESTINOS};

/*Almacena la velocidad de cada vehículo disponible*/
param velocidad{i in VEHICULOS};

/*Almacena el consumo de cada vehículo disponible*/
param consumo{i in VEHICULOS};

/*Almacena la distancia desde Madrid hasta el destino*/
param dist_destinos{j in DESTINOS};

/*Almacena el número de horas máximo para realizar la entrega*/
param max_horas_entrega;

/*Almacena la matriz de asignación de horas a cada trabajador por tarea*/
var asig_horas {i in TRABAJADORES, j in TAREAS}, integer>=0;

/*Almacena la matriz binaria de la asignación de vehículos a trayectos*/
var asig_vehic {i in VEHICULOS, j in DESTINOS}, binary;

#Funcion objetivo
/*Minimiza el coste de todo el problema, sumando las funciones de coste
de ambos problemas: asignación de horas por trabajador y tarea multiplicado 
por el coste por hora de trabajador en tarea, sumado a la asignación de vehículos de 
cada trayecto por el coste de ese vehículo para realizar el trayecto*/
minimize cost: sum{i in TRABAJADORES, j in TAREAS} asig_horas [i,j] * remuneracion[i,j] + 2*(sum{i in VEHICULOS, j in DESTINOS_1}asig_vehic[i,j]*(dist_destinos[j]*(consumo[i]/velocidad[i])))+
(sum{i in VEHICULOS, j in DESTINOS_2}asig_vehic[i,j]*(dist_destinos[j]*(consumo[i]/velocidad[i])));

#Restricciones <=
/*Restricciones de primer problema*/
s.t. jornada8horas {i in TRABAJADORES} : sum{j in TAREAS} asig_horas [i,j]  <= max_horas;

/*Esta restricción limita la matriz de asignación de horas al máximo de horas por 
trabajador en cada tarea*/
s.t. horas_max_tarea {i in TRABAJADORES, j in TAREAS} : asig_horas[i,j] <= tiempo_max[i,j];

/*Esta restricción compara la matriz las remuneracioens de cada trabajados con la suya
y la de sus compañeros, para poder duplicar la tabla para la comparación, le asignamos dos
índices diferentes*/
s.t. remuneracion_max {i in TRABAJADORES, ii in TRABAJADORES} : sum{j in TAREAS} asig_horas[i,j]*remuneracion[i,j] <= 
2*(sum{j in TAREAS} asig_horas [ii,j]*remuneracion[ii,j]);

/*Restricciones del segundo problema*/
/*Esta restricción limita el número del kilómetros de los tres camiones
que menos consumen, para que los que más consumen hagan al menos el 50% de km recorridos
por los que menos consumen. Dividimos entre DESTINOS_1 y DESTINOS_2 para poder 
duplicar el valor de los DESTINOS_1 que realizan un ida y vuelta*/
s.t. min_km : 0.5*(sum{i in BCONSUMO, j in DESTINOS_1} 2*asig_vehic [i,j]*(dist_destinos[j])) + 
(sum{i in BCONSUMO, j in DESTINOS_2} asig_vehic [i,j]*(dist_destinos[j])) <= 
(sum{i in ACONSUMO, j in DESTINOS_1} 2*asig_vehic [i,j]*(dist_destinos[j])) + 
(sum{i in ACONSUMO, j in DESTINOS_2} asig_vehic [i,j]*(dist_destinos[j]));

/*Esta restricción limita el número de horas del proyecto a 15.5 horas en total.
para ello tenemos que diferenciar entre los destinos porque el tiempo será el doble para
los destinos de recogida.*/
s.t. horas_max_trans {j in DESTINOS_1, jj in DESTINOS_2} : 2*(sum{i in VEHICULOS}asig_vehic[i,j]*(dist_destinos[j]/velocidad[i]))+
(sum{i in VEHICULOS}asig_vehic[i,jj]*(dist_destinos[jj]/velocidad[i])) <= max_horas_entrega;

/*Esta restricción limita las opciones de asignación de los DESTINOS_1 a las preferencias
de los conductores*/
s.t. preferencias_trans {i in VEHICULOS, j in DESTINOS_1} : asig_vehic[i,j] <= preferencias[i,j];


#Restricciones de igualdad
/*Restricciones de igualdad del primer problema*/
/*Esta restricción obliga a que las tareas tengan un número de horas invertidas 
especificado en horas_por_tarea*/
s.t. i_horas {j in TAREAS} : sum {i in TRABAJADORES} asig_horas[i,j] = horas_por_tarea[j];

/*Restriscciones de igualdad del segundo modelo*/
/*Esta restricción limita al número de vehículos asignados a cada trayecto
para que sea un único vehículo*/
s.t. i_binaria {j in DESTINOS} : sum{i in VEHICULOS}asig_vehic[i,j] = 1;

data ;

/*Sets relacionados con el primer problema*/
/*Objetos dentro del set TRABAJADORES*/
set TRABAJADORES :=
Adrian
Pedro
Maria;

/*Objetos dentro del set TAREAS*/
set TAREAS :=
Tarea1
Tarea2
Tarea3;

/*Sets relacionados con el segundo problema*/
/*Objetos dentro del set VEHICULOS*/
set VEHICULOS :=
Camion1
Camion2
Camion3
Camion4
Camion5
Camion6
Tren1
Tren2;

/*Subset relacionado con el set VEHICULOS, vehículos de alto consumo*/
set ACONSUMO := 
Camion1 
Camion4 
Camion5;

/*Subset relacionado con el set VEHICULOS, vehículos de bajo consumo*/
set BCONSUMO :=
Camion2
Camion3
Camion6;

/*Objetos dentro del set DESTINOS*/
set DESTINOS :=
Madrid_Leon
Madrid_Caceres
Madrid_Sevilla
Madrid_Soria
Madrid_Valencia;

/*Subset relacionado con el set DESTINOS, destinos de recogida(ida y vuelta)*/
set DESTINOS_1 :=
Madrid_Leon
Madrid_Caceres
Madrid_Sevilla
Madrid_Soria;

/*Subset relacionado con el set DESTINOS, destino de entrega(sólo ida)*/
set DESTINOS_2 :=
Madrid_Valencia;

/*Matriz con los coste/hora de cada trabajador*/
param remuneracion :
        Tarea1 Tarea2 Tarea3 :=
Adrian      10  7  5
Pedro       8   5  3
Maria       7   6  4;

/*Matriz con el tiempo máximo de disposición de cada trabajador para cada tarea*/
param tiempo_max :
	Tarea1 Tarea2 Tarea3 :=
Adrian      5   4  2
Pedro       6   3  4
Maria       4   1  3;

/*Vector de datos con la horas necesarias a dedicar para cada tarea*/
param horas_por_tarea :=
Tarea1	12
Tarea2	8
Tarea3	4;

/*Número máximo de horas asignadas por trabajador*/
param max_horas := 8;

/*Matriz binaria en representación de preferencias de conductores para DESTINOS_1.
Destinos con un 0 no entran dentro de las preferencias, y destinos con un 1 
entran dentro de las preferencias*/
param preferencias :
    Madrid_Leon Madrid_Caceres Madrid_Sevilla Madrid_Soria :=
Camion1  	0	0	0	1
Camion2  	0	1	1	0
Camion3		0	0	1 	1
Camion4		0	1	1	1
Camion5		1	1	1	1
Camion6		0	1	0	1
Tren1		0	0	0	0
Tren2		0	0	0	0;

/*Vector de datos que almacena la velocidad media de cada vehículo*/
param velocidad :=
Camion1	80
Camion2	70
Camion3	50
Camion4	90
Camion5	85
Camion6	30
Tren1	100
Tren2	150;

/*Vector de datos que almacena el consumo medio de cada vehículo*/
param consumo :=
Camion1	15
Camion2	7
Camion3	6
Camion4	17
Camion5	18
Camion6	2
Tren1	20
Tren2	30;

/*Vector de datos que almacena la distancia entre Madrid y los diferentes destinos*/
param dist_destinos :=
Madrid_Leon			340	
Madrid_Caceres		300
Madrid_Sevilla		530
Madrid_Soria		230
Madrid_Valencia		360;

/*Número de horas máximo para realizar la recogida y entrega de los productos*/
param max_horas_entrega := 15.5;

end;