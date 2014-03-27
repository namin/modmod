all: miniML miniC

GENFILES=miniMLparser.ml miniMLparser.mli miniMLlexer.ml \
  miniCparser.ml miniCparser.mli miniClexer.ml

MINIML=modules.cmo miniML.cmo miniMLparser.cmo miniMLlexer.cmo miniMLmain.cmo

miniML: $(MINIML)
	ocamlc -o miniML $(MINIML)

miniMLparser.ml miniMLparser.mli: miniMLparser.mly
	ocamlyacc miniMLparser.mly

miniMLlexer.ml: miniMLlexer.mll
	ocamllex miniMLlexer.mll

MINIC=modules.cmo miniC.cmo miniCparser.cmo miniClexer.cmo miniCmain.cmo

miniC: $(MINIC)
	ocamlc -o miniC $(MINIC)

miniCparser.ml miniCparser.mli: miniCparser.mly
	ocamlyacc miniCparser.mly

miniClexer.ml: miniClexer.mll
	ocamllex miniClexer.mll

clean:
	rm -f *.cm?
	rm -f miniML
	rm -f miniC
	rm -f $(GENFILES)

.SUFFIXES: .cmo .ml .cmi .mli

.ml.cmo:
	ocamlc -c $<
.mli.cmi:
	ocamlc -c $<

include .depend

depend: $(GENFILES)
	ocamldep *.ml *.mli > .depend

