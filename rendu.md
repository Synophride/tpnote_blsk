## TP noté de sémantique et types -- Julien

Les deux premiers exercices (dont le bonus) ont été faits.
Le troisième a été implémenté, mais très peu testé donc il n'est probablement pas correct. 


L'archive contient -- en plus de ce fichier texte -- le code (Inference.ml) un (maigre) fichier de test (InferenceTest.ml), un makefile compilant et lançant le programme de test.


Pour les opérateurs, j'ai considéré qu'on opérateur à plusieurs opérandes représentait une fonction prenant deux paramètres (et pas une fonction prenant une paire en paramètre).


Par conséquent, l'expression '4+3' serait modélisée par
App( App( Op("+"), Int(4)), Int(3))
et non
App( Op("+"), Pair( Int 4, Int 3))
