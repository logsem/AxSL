.PHONY : all header

all :
	dune build


header:
	rm -rf ./pub
	mkdir -p ./pub
	cp -r system-semantics theories .github ./pub/
	find . -maxdepth 1 -type f ! -name ".*" ! -name "TODO.md" -exec cp {} ./pub/ \;
	find ./pub/theories -name "*.v" -type f -exec headache -c headache-config -h header {} \;