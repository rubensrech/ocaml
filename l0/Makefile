PARSER_PATH=parser/

all: l_zero

l_zero:
	ocamlbuild l0BigStep.native
	ocamlbuild l0SmallStep.native

# Clean
clean:
	ocamlbuild -clean