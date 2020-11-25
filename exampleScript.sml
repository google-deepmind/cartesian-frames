open HolKernel boolLib bossLib boolSimps pred_setTheory Parse stringTheory cf0Theory

val _ = new_theory"example";

Definition runs_cf1_def:
  runs_cf1 = <| agent := { "u"; "n" }; env := { "r"; "s" };
                world := {"ur"; "us"; "nr"; "ns"};
                eval := λa e. a ++ e |>
End

Theorem sup_closure_example:
  sup_closure runs_cf1.world {{"ur"; "us"};{"nr";"ns"}} =
  {{"ur"; "us"};{"nr";"ns"};
   {"ur";"us";"nr"};{"ur";"us";"ns"};{"nr";"ns";"ur"};{"nr";"ns";"us"};
   runs_cf1.world}
Proof
  rw[SET_EQ_SUBSET]
  >- (
    rw[sup_closure_def, runs_cf1_def, SUBSET_DEF, SET_EQ_SUBSET]
    \\ fsrw_tac[DNF_ss][]
    \\ metis_tac[] )
  \\ rw[sup_closure_def]
  \\ srw_tac[DNF_ss][]
  \\ EVAL_TAC
QED

Theorem sub_closure_example:
  sub_closure runs_cf1.world {{"ur"; "us"};{"nr";"ns"}} =
  {{"ur"; "us"};{"nr";"ns"};
   {"ur"};{"us"};{"nr"};{"ns"};{}}
Proof
  rw[SET_EQ_SUBSET]
  \\ TRY (
    rw[sub_closure_def, runs_cf1_def]
    \\ fsrw_tac[DNF_ss][]
    \\ NO_TAC)
  \\ rw[sub_closure_def, runs_cf1_def, SUBSET_DEF]
  \\ spose_not_then strip_assume_tac \\ fs[EXTENSION]
  \\ metis_tac[]
QED

Theorem runs1_ensure:
  ensure runs_cf1 = sup_closure runs_cf1.world {{"ur"; "us"}; {"nr"; "ns"}}
Proof
  rw[ensure_def, runs_cf1_def, sup_closure_example]
  \\ rw[SET_EQ_SUBSET, SUBSET_DEF]
  \\ fsrw_tac[DNF_ss][] \\ metis_tac[]
QED

Theorem runs1_prevent:
  prevent runs_cf1 = sub_closure runs_cf1.world {{"ur";"us"};{"nr";"ns"}}
Proof
  rw[prevent_def, runs_cf1_def, sub_closure_example]
  \\ rw[SUBSET_DEF]
  \\ rw[Once EXTENSION]
  \\ EQ_TAC \\ rw[] \\ fsrw_tac[DNF_ss][]
  \\ spose_not_then strip_assume_tac
  \\ fsrw_tac[DNF_ss][EXTENSION]
  >- PROVE_TAC[]
  \\ metis_tac[]
QED


Theorem runs1_ctrl:
  ctrl runs_cf1 = {{"ur";"us"};{"nr";"ns"}}
Proof
  rw[ctrl_def, runs1_prevent, runs1_ensure, sub_closure_example, sup_closure_example]
  \\ rw[runs_cf1_def]
  \\ rw[EXTENSION] \\ metis_tac[]
QED

Definition runs_cf2_def:
  runs_cf2 = <| agent := {"u";"n";"run";"sun"};
                env := {"r";"s"};
                world := runs_cf1.world;
                eval := λa e. (if LENGTH a < 2 then EL 0 a else
                               if EL 0 e = EL 0 a then EL 1 a else EL 2 a)::e |>
End

Theorem runs2_ctrl:
  ctrl runs_cf2 = {{"ur";"us"};{"nr";"ns"};{"ur";"ns"};{"nr";"us"}}
Proof
  rw[ctrl_def, ensure_def, prevent_def, runs_cf2_def, runs_cf1_def, SUBSET_DEF]
  \\ rw[Once EXTENSION]
  \\ EQ_TAC \\ rw[] \\ fs[]
  \\ spose_not_then strip_assume_tac
  \\ fsrw_tac[DNF_ss][]
  \\ fs[Once EXTENSION]
  \\ metis_tac[]
QED

Definition runs_cf3_def:
  runs_cf3 = runs_cf2 with <| env := "m" INSERT runs_cf2.env;
                              world := "m" INSERT runs_cf2.world;
                              eval := λa e. if e = "m" then "m" else runs_cf2.eval a e |>
End

Theorem runs3_ensure:
  ensure runs_cf3 =
    sup_closure runs_cf3.world {{"ur";"us";"m"};{"nr";"ns";"m"};{"ur";"ns";"m"};{"nr";"us";"m"}}
Proof
  rw[ensure_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ rw[sup_closure_def]
  \\ rw[Once EXTENSION]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w` \\ Cases_on`x ⊆ w` \\ fs[]
  \\ EQ_TAC \\ rw[] \\ fsrw_tac[DNF_ss][]
QED

Theorem runs3_prevent:
  prevent runs_cf3 =
    sub_closure runs_cf3.world {{"ur";"us"};{"nr";"ns"};{"ur";"ns"};{"nr";"us"}}
Proof
  rw[prevent_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ rw[sub_closure_def]
  \\ rw[Once EXTENSION]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w` \\ Cases_on`x ⊆ w` \\ fs[]
  \\ EQ_TAC >- (
    rw[] \\ fsrw_tac[DNF_ss][]
    \\ fsrw_tac[DNF_ss][SUBSET_DEF]
    \\ spose_not_then strip_assume_tac \\ fsrw_tac[DNF_ss][Once EXTENSION, Abbr`w`]
    \\ metis_tac[] )
  \\ rw[] \\ fsrw_tac[DNF_ss][Abbr`w`, SUBSET_DEF]
  \\ Cases_on`"m" ∈ x` \\ fs[]
  \\ Cases_on`"ur" ∈ x` \\ fs[] \\ res_tac \\ fs[]
  \\ Cases_on`"nr" ∈ x` \\ fs[] \\ res_tac \\ fs[]
  \\ Cases_on`"ns" ∈ x` \\ fs[] \\ res_tac \\ fs[]
  \\ Cases_on`"us" ∈ x` \\ fs[] \\ res_tac \\ fs[]
QED

Theorem runs3_ctrl:
  ctrl runs_cf3 = ∅
Proof
  rw[ctrl_def, runs3_ensure, runs3_prevent]
  \\ rw[sup_closure_def, sub_closure_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ rw[GSYM DISJOINT_DEF]
  \\ rw[IN_DISJOINT]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w`
  \\ Cases_on`x ⊆ w` \\ fs[]
  \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[Abbr`w`] \\ fs[SUBSET_DEF]
  \\ res_tac \\ fs[]
QED

val _ = export_theory();
