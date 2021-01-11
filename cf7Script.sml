(*
Copyright 2020 Google LLC

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

open HolKernel boolLib bossLib Parse dep_rewrite
  pred_setTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf6Theory

val _ = new_theory"cf7";

Definition is_subsum_def:
  is_subsum c d s ⇔
    s.world = (sum c d).world ∧
    s.agent = (sum c d).agent ∧
    s.env ⊆ (sum c d).env ∧
    (∀a. s.eval a = restrict ((sum c d).eval a) s.env) ∧
    c ≃ (mk_cf <| world := c.world;
                  agent := IMAGE (encode_sum o INL) c.agent;
                  env := s.env;
                  eval := s.eval |>) -: c.world ∧
    d ≃ (mk_cf <| world := d.world;
                  agent := IMAGE (encode_sum o INR) d.agent;
                  env := s.env;
                  eval := s.eval |>) -: d.world
End

Definition is_subtensor_def:
  is_subtensor c d t ⇔
    t.world = (tensor c d).world ∧
    t.agent = (tensor c d).agent ∧
    t.env ⊆ (tensor c d).env ∧
    (∀a. t.eval a = restrict ((tensor c d).eval a) t.env) ∧
    c ≃ (mk_cf <| world := c.world;
                  agent := c.agent;
                  env := IMAGE encode_pair (d.agent × t.env);
                  eval := λa e.
                    t.eval (encode_pair (a, FST (decode_pair e)))
                           (SND (decode_pair e)) |>) -: c.world ∧
    d ≃ (mk_cf <| world := d.world;
                  agent := d.agent;
                  env := IMAGE encode_pair (c.agent × t.env);
                  eval := λa e.
                    t.eval (encode_pair (FST (decode_pair e), a))
                           (SND (decode_pair e)) |>) -: d.world
End

Theorem finite_subsum:
  finite_cf c ∧ finite_cf d ∧ is_subsum c d s ⇒ finite_cf s
Proof
  rw[is_subsum_def]
  \\ `finite_cf (sum c d)` by imp_res_tac finite_sum
  \\ fs[finite_cf_def]
  \\ metis_tac[SUBSET_FINITE]
QED

Theorem wf_subsum:
  wf c ∧ wf d ∧ is_subsum c d s ⇒ wf s
Proof
  strip_tac
  \\ `wf (sum c d)` by imp_res_tac wf_sum
  \\ fs[wf_def]
  \\ mp_tac finite_subsum \\ simp[] \\ strip_tac
  \\ fs[is_subsum_def]
  \\ simp[restrict_def]
  \\ gs[SUBSET_DEF]
  \\ rw[]
QED

Theorem finite_subtensor:
  finite_cf c ∧ finite_cf d ∧ is_subtensor c d s ⇒ finite_cf s
Proof
  rw[is_subtensor_def]
  \\ `finite_cf (tensor c d)` by imp_res_tac finite_tensor
  \\ fs[finite_cf_def]
  \\ metis_tac[SUBSET_FINITE]
QED

Theorem wf_subtensor:
  wf c ∧ wf d ∧ is_subtensor c d s ⇒ wf s
Proof
  strip_tac
  \\ `wf (tensor c d)` by imp_res_tac wf_tensor
  \\ fs[wf_def]
  \\ mp_tac finite_subtensor \\ simp[] \\ strip_tac
  \\ fs[is_subtensor_def]
  \\ simp[restrict_def]
  \\ gs[SUBSET_DEF]
  \\ rw[]
QED

val _ = export_theory();
