.PHONY : all header publish

all :
	dune build


header:
	rm -rf ./pub
	mkdir -p ./pub
	cp -r system-semantics theories .github ./pub/
	find . -maxdepth 1 -type f ! -name ".*" ! -name "TODO.md" -exec cp {} ./pub/ \;
	cp .gitignore .gitmodules ./pub/ 2>/dev/null || true
	find ./pub/theories -name "*.v" -type f -exec headache -c headache-config -h LICENSE {} \;

publish:
	rm -rf ./pub-git
	git clone https://github.com/logsem/AxSL.git ./pub-git
	find ./pub-git -mindepth 1 -maxdepth 1 ! -name '.git' ! -name '.gitignore' -exec rm -rf {} +
	cp -r ./pub/* ./pub-git/
	cd ./pub-git && \
	git add -A && \
	git commit -m "Release update" && \
	git push origin main
	rm -rf ./pub-git