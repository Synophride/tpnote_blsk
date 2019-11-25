
r : ITest
	./ITest

ITest : Inference.ml InferenceTest.ml
	ocamlc Inference.ml InferenceTest.ml -o ITest

clean :
	rm *.cmi *.cmo ITest \#Inf* 
