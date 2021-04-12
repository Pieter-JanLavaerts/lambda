all: build run

build: *.ml *.mly *.mll
	dune build 

run: _build/default/lambda.exe
	dune exec ./lambda.exe
