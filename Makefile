all: main.exe

main.exe:
	dune build

.PHONY: clean

clean:
	dune clean
