# draw file dependency graph for /theroies
# require running `dune build` first to generate the .d file

( echo "digraph interval_deps {" ;
  echo "node [shape=ellipse, style=filled, URL=\"html/Interval.\N.html\", color=white];";
  (cat "./_build/default/theories/.self.theory.d") |
    # replace / with ., and remove .vos files
    sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
    while read src dst; do
        # skip coq library
        if [ $(echo "$src" | grep -c "lib.coq") -eq 0 ]
        then
            echo "\"$src\" [fillcolor=yellow];"
        fi
      for d in $dst; do
        # skip coq library
          if [ $(echo "$d" | grep -c "lib.coq") -eq 0 ]
          then
        # skip vos files
          if [ $(echo "$d" | grep -c "vos") -eq 0 ]
          then
              echo "\"$src\" -> \"${d%.vo}\" ;"
              fi
          fi
      done
    done;
  echo "}"
) | tred > deps.dot

dot -T png deps.dot > deps.png
# dot -T cmap deps.dot | sed -e 's,>$,/>,' > deps.map
