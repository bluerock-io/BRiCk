# _CoqProject generator

This script will generate an approximate `_CoqProject` file from a dune project, by parsing
all `coq.theory` stanzas in `dune` files to generate `-Q` mappings.

## Installing dependencies

Use `pip install -r python_requirements.txt` or the equivalent for your Python
virtual environment.

## Invoke

Run `gen-_CoqProject-dune.sh > _CoqProject` in the `your_dune_workspace` directory.

## Customize Coq warnings

If desired, create a `your_dune_workspace/coq.flags` file containing a
`_CoqProject` snippet, for instance:

```
# Example warning settings:
-arg -w -arg -notation-overridden
```

An absent `coq.flags` is equivalent to an empty one.
