rocq-tc-db-info
====================
The rocq-tc-db-info package provides a vernacular command to report
transparent terms in hint (typeclass) patterns.

Motivation
=============
Coq uses discrimination nets to perform coarse-grained prefiltering during
typeclass search. Only those hints that pass the prefiltering stage result in an
application attempt. Since applying hints involves unification, hint search
performance largely depends on filtering out as many useless attempts as
possible in the prefiltering stage.

Apart from obvious different in term shapes, the main benefit of this
prefiltering is only really unlocked when users carefully control term opacity
in the database (using `Hint Opaque`). However, it is extremely difficult to
maintain good opacity settings in projects that are still in development, where
new terms and instances are added regularly.

rocq-tc-db-info aims to provide tools to make this kind of maintenance easier
(and, possibly, to eventually automate parts of it). For now, we provide a
vernacular command that outputs a summary of transparent terms found in a given
database in hint patterns for a given class.

Usage
=======
The plugin provides the `HintDb Opacity Info` vernacular command. Example:

```coq
Require Import tc_db_info.tc_db_info.
HintDb Opacity Info <my_db> For <my_class>.
```

The vernacular command reports transparent terms found in hint patterns *by
depth*, starting with top-level terms. This is because transparent top-level (depth 1)
terms are likely to be more interesting to users than those buried deep within
sub terms.

Example output:
```
Db: test
Class: C
Transparent terms per depth
Depth 1
  tt' (modes {-}) in Hint Resolve [Exact] (exact Cu')
  unit' (modes {!}) in Hint Resolve [Exact] (exact Cu')
```

Interpretation of the Output
=====================================
The interpretation of the output depends on the exact use case of hints and
will vary from project to project. A good rule of thumb is to make sure that
there are no transparent top-level terms as those will likely generate the lion
share of failing hint applications.

However, there are also cases where transparent sub terms of opaque top-level
terms are problematic for performance.

Determining if any transparent term (sub term or top-level term) poses a
performance problem can be difficult. Currently, this is best done by reading
debug output of long-running searches with `Set Typeclasses Debug Verbosity 2`.
Hints that yield many failing applications (in particular, applications
resulting in unification failures) can then be cross-referenced with the output
of `HintDb Opacity Info` to find transparent (sub) terms that could improve the
prefiltering.

Options
=========
There are two options to control the behavior and output of `HintDb Opacity
Info`.

* `Set HintDb Opacity Info Fully Qualified` enables the fully qualified printing
  of transparent terms, i.e. it always prints the full module path. The option
  is disabled by default.
* `Set HintDb Opacity Info Ignore Outputs.` ignores transparent terms found in
  class arguments that are marked as outputs (using `Hint Mode`). This is useful
  when the outputs of a class are not fed back into typeclass search or if they
  are reduced/normalized in a way that will remove transparent terms before they
  are used for the next typeclass search. The option is disabled by default.
