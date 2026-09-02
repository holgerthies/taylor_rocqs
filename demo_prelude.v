(** Common imports for the IVP solver demo *)

Require Export algebra ode polynomial functions.
From Coq Require Export Psatz.

Require Export List tuple.
From Coq Require Export Setoid.
Require Export Coq.Classes.SetoidClass.

Require Export combinatorics.
Require Export archimedean realanalytic pivp coqrationals.

From Coq Require Export QArith.

Export ListNotations.

Global Open Scope poly_scope.

Require Export interval interval_string iode.
Require Export Coq.Strings.String.
SetPythonPath "/Users/holgerthies/miniconda3/bin/python3".
Global Open Scope string_scope.
