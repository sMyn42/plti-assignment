all: types proofs

types: types.ml
	ocamlbuild -use-ocamlfind types.byte

proofs: proof_comm.ml
	ocamlbuild -use-ocamlfind proof_comm.byte

clean:
	rm -rf _build *.byte