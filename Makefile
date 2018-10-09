PARSER_PATH=parser/

all: l_zero l_um

l_um:
	ocamlbuild l1.native -I $(PARSER_PATH)

l_zero:
	ocamlbuild l0/l0BigStep.native
	ocamlbuild l0/l0SmallStep.native

# Clean
clean:
	ocamlbuild -clean