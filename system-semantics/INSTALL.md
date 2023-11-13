## Software Dependencies

### Coq libraries

#### Coq Sail

```
git clone https://github.com/rems-project/coq-sail
```

Then (optionally), in that repository, if you want the version used for development, do:
```
git checkout aeca2c5
```

Then you can install `coq-sail` with `opam pin .` in the repository. It should
install its own dependencies such as `coq-bbv`.
