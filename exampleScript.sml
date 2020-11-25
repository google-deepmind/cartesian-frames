open HolKernel boolLib bossLib boolSimps pred_setTheory Parse stringTheory stringLib cf0Theory

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
  \\ Cases_on`x = {}` \\ fs[]
  \\ Cases_on`x` \\ fsrw_tac[DNF_ss][] \\ rw[INSERT_EQ_SING]
  \\ Cases_on`t` \\ fsrw_tac[DNF_ss][] \\ rw[INSERT_EQ_SING]
  \\ fs[EXTENSION] \\ metis_tac[]
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
  \\ strip_tac \\ rpt BasicProvers.var_eq_tac
  THENL (map (exists_tac o fromMLstring) ["n", "u", "sun", "run"])
  \\ rw[] \\ CCONTR_TAC \\ fs[SUBSET_DEF] \\ res_tac \\ fs[]
QED

fun tails [] = []
  | tails (x::y) = (x,y) :: tails y

val envs = ["m","us","ur","ns","nr"]
val ineqs =
  map (fn (x, r) =>
         map (fn y => EVAL(mk_eq(fromMLstring x, fromMLstring y))) r)
      (tails envs) |> List.concat

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
  \\ metis_tac ineqs
QED

Theorem runs1_obs:
  obs runs_cf1 = union_closure {runs_cf1.world}
Proof
  rw[union_closure_sing, obs_def, EXTENSION, SUBSET_DEF, runs_cf1_def, ifs_def]
  \\ rw[Once EQ_IMP_THM]
  \\ fsrw_tac[DNF_ss][]
  \\ metis_tac[]
QED


Theorem wf_runs2[simp]:
  wf runs_cf2
Proof
  rw[wf_def, runs_cf2_def, runs_cf1_def]
QED

Theorem runs2_obs:
  obs runs_cf2 = union_closure {{"ur";"nr"}; {"us";"ns"}}
Proof
  qmatch_goalsub_abbrev_tac`union_closure s`
  \\ `union_closure s = {{}; runs_cf1.world} ∪ s`
  by (
    rw[Abbr`s`, union_closure_def, runs_cf1_def]
    \\ rw[Once EXTENSION]
    \\ Cases_on`x = {}` \\ fsrw_tac[DNF_ss][]
    \\ Cases_on`x = {"us";"ns"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"us";"ns"}}` \\ simp[])
    \\ Cases_on`x = {"ur";"nr"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"ur";"nr"}}` \\ simp[])
    \\ Cases_on`x = {"ur";"us";"nr";"ns"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"ur";"nr"};{"us";"ns"}}` \\ simp[] \\ simp[EXTENSION] \\ metis_tac[])
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ Cases_on`s` \\ fs[] \\ rw[] \\ fs[]
    \\ Cases_on`t` \\ fs[] \\ rw[] \\ fs[] \\ rw[] \\ fs[] \\ rw[]
    \\ fs[EXTENSION] \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ once_rewrite_tac[SET_EQ_SUBSET]
  \\ reverse conj_asm2_tac >- (
    simp[SUBSET_DEF, GSYM CONJ_ASSOC]
    \\ conj_asm1_tac >- simp[obs_empty]
    \\ conj_tac >- (
      first_assum(mp_then Any mp_tac obs_compl)
      \\ simp[runs_cf2_def] )
    \\ pop_assum kall_tac
    \\ simp[Abbr`s`]
    \\ rw[obs_def] \\ TRY (rw[runs_cf2_def, runs_cf1_def, SUBSET_DEF] \\ NO_TAC)
    \\ rw[ifs_def]
    \\ fs[runs_cf2_def, runs_cf1_def] \\ rw[]
    \\ TRY(qexists_tac`"u"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"n"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"run"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"sun"` \\ rw[] \\ fs[] \\ NO_TAC))
  \\ rw[SUBSET_DEF]
  \\ CCONTR_TAC \\ fs[]
  \\ qpat_x_assum`x ∈ _`mp_tac
  \\ rw[obs_def, runs_cf2_def]
  \\ Cases_on`x ⊆ runs_cf1.world` \\ fs[]
  \\ fs[Abbr`s`]
  \\ Cases_on`x = {"ur"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"u"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"nr"}`
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur"}`
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ur";"ns"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"ns"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"nr"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"ur";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"us";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ `F` suffices_by rw[]
  \\ qpat_x_assum`x ⊆ _`mp_tac
  \\ fs[runs_cf1_def]
  \\ simp[GSYM IN_POW]
  \\ simp[POW_EQNS]
  \\ fs[INSERT_COMM]
QED

val _ = export_theory();
