(*
Copyright 2021 DeepMind Technologies Limited.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

open HolKernel boolLib bossLib Parse
  pred_setTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf5Theory

val _ = new_theory"ex5";

Definition team_def:
  team = cfbot {"x";"y"} {"x";"y"}
End

Definition alice_def:
  alice = mk_cf <| world := {"x"; "y"};
    agent := {"x"; "y"; "b"};
    env := {"x"; "y"};
    eval := λa e. if a = "b" then e else a |>
End

Theorem team_in_chu_objects[simp]:
  team ∈ chu_objects {"x";"y"}
Proof
  rw[team_def]
QED

Theorem alice_in_chu_objects[simp]:
  alice ∈ chu_objects {"x";"y"}
Proof
  rw[alice_def, in_chu_objects, finite_cf_def]
  \\ rw[image_def, SUBSET_DEF]
QED

Theorem alice_subagent_team:
  alice ◁ team -: {"x";"y"}
Proof
  rw[subagent_covering]
  \\ rw[covering_subagent_def]
  \\ qexists_tac`""`
  \\ simp[Once team_def, cfbot_def]
  \\ qexists_tac`mk_chu_morphism alice team <| map_agent := λa. if a = "b" then e else a;
                                               map_env := K e |>`
  \\ reverse conj_tac >- simp[mk_chu_morphism_def, restrict_def, team_def, cfbot_def]
  \\ simp[maps_to_in_chu]
  \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ `team.agent = alice.env` by simp[team_def, alice_def, cfbot_def]
  \\ `alice.agent = "b" INSERT alice.env` by (
    simp[alice_def] \\ simp[EXTENSION] \\ metis_tac[] )
  \\ simp[]
  \\ conj_tac >- metis_tac[]
  \\ qpat_x_assum`e ∈ _`mp_tac
  \\ EVAL_TAC
  \\ rw[]
QED

Theorem team_subagent_alice:
  team ◁ alice -: {"x";"y"}
Proof
  rw[subagent_covering, covering_subagent_def]
  \\ pop_assum mp_tac
  \\ rw[Once team_def, cfbot_def]
  \\ qexists_tac`"x"`
  \\ simp[Once alice_def]
  \\ qexists_tac`mk_chu_morphism team alice <| map_agent := I; map_env := K "" |>`
  \\ simp[maps_to_in_chu, is_chu_morphism_def, mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ EVAL_TAC \\ rw[]
QED

Theorem nontrivial_mutual_subagents:
  mutual_subagents {"x";"y"} alice team
Proof
  metis_tac[mutual_subagents_def, alice_subagent_team, team_subagent_alice]
QED

val _ = export_theory();
