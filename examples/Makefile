OCAMLC = ocamlc -ppx ../ppx_measure.native


example:
	$(OCAMLC) -dsource example.ml -o example.byte
	rm -rf *.cm*

show:
	ocamlfind ppx_tools/dumpast example.ml

clean:
	rm -rf *~
	rm -rf \#*
	rm -rf *.cm*
	rm -rf *.byte
