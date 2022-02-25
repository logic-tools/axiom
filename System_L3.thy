(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_L3 imports System_L1 begin

text \<open>System L3 from Jan Lukasiewicz: ???\<close>

text \<open>Derivations are taken from: On Axiom Systems of Propositional Calculi. III
                                  by Yoshinari Arai (1965)\<close>

inductive L3 (\<open>\<LL>\<^sub>3\<close>) where
  L3_MP: \<open>\<LL>\<^sub>3 q\<close> if \<open>\<LL>\<^sub>3 p\<close> and \<open>\<LL>\<^sub>3 (p \<rightarrow> q)\<close> |
  L3_1:  \<open>\<LL>\<^sub>3 (p \<rightarrow> (q \<rightarrow> p))\<close> |
  L3_2:  \<open>\<LL>\<^sub>3 ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> |
  L3_3:  \<open>\<LL>\<^sub>3 (((\<sim> p) \<rightarrow> (\<sim> q)) \<rightarrow> (q \<rightarrow> p))\<close>

lemma L3_4: \<open>\<LL>\<^sub>3 ((\<sim> p) \<rightarrow> (((\<sim> q) \<rightarrow> (\<sim> p)) \<rightarrow> (p \<rightarrow> q)))\<close>
  using L3_1 L3_3 L3_MP by metis

lemma L3_5: \<open>\<LL>\<^sub>3 ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close>
  using L3_1 L3_2 L3_4 L3_MP by metis

lemma L3_6: \<open>\<LL>\<^sub>3 (((\<sim> q) \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> p))\<close>
  using L3_2 L3_5 L3_MP by metis

lemma L3_7: \<open>\<LL>\<^sub>3 (q \<rightarrow> (((\<sim> q) \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> p)))\<close>
  using L3_1 L3_6 L3_MP by metis

lemma L3_8: \<open>\<LL>\<^sub>3 (q \<rightarrow> ((\<sim> q) \<rightarrow> p))\<close>
  using L3_1 L3_2 L3_7 L3_MP by metis

lemma L3_9: \<open>\<LL>\<^sub>3 (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close>
  using L3_8.

lemma L3_10: \<open>\<LL>\<^sub>3 ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r))))\<close>
  using L3_1 L3_2 L3_MP by metis

lemma L3_11: \<open>\<LL>\<^sub>3 ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L3_1 L3_2 L3_10 L3_MP by metis

lemma L3_12: \<open>\<LL>\<^sub>3 (((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L3_2 L3_11 L3_MP by metis

lemma L3_13: \<open>\<LL>\<^sub>3 ((p \<rightarrow> q) \<rightarrow> (((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r))))\<close>
  using L3_1 L3_12 L3_MP by metis

lemma L3_14: \<open>\<LL>\<^sub>3 ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L3_1 L3_2 L3_13 L3_MP by metis

lemma L3_15: \<open>\<LL>\<^sub>3 (((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L3_2 L3_MP by metis

lemma L3_16: \<open>\<LL>\<^sub>3 ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> p))\<close>
  using L3_1 L3_2 L3_MP by metis

lemma L3_17: \<open>\<LL>\<^sub>3 (p \<rightarrow> p)\<close>
  using L3_1 L3_16 L3_MP by metis

lemma L3_18: \<open>\<LL>\<^sub>3 ((p \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> p))\<close>
  using L3_1 L3_17 L3_MP by metis (* under substitution this lemma is the same as L3_16 *)

lemma L3_19: \<open>\<LL>\<^sub>3 ((p \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> q))\<close>
  using L3_15 L3_18 L3_MP by metis

lemma L3_20: \<open>\<LL>\<^sub>3 (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> ((q \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r))))\<close>
  using L3_11.

lemma L3_21: \<open>\<LL>\<^sub>3 (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> q)))\<close>
  using L3_1 L3_MP by metis

lemma L3_22: \<open>\<LL>\<^sub>3 (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using L3_2 L3_20 L3_21 L3_MP by metis

lemma L3_23: \<open>\<LL>\<^sub>3 ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using L3_2 L3_11 L3_22 L3_MP by metis

lemma L3_24: \<open>\<LL>\<^sub>3 (((\<sim> q) \<rightarrow> (\<sim> p)) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L3_3 L3_11 L3_14 L3_MP by metis

lemma L3_25: \<open>\<LL>\<^sub>3 (((\<sim> q) \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using L3_6 L3_11 L3_24 L3_MP by metis

lemma L3_26: \<open>\<LL>\<^sub>3 (((\<sim> q) \<rightarrow> q) \<rightarrow> (((\<sim> q) \<rightarrow> q) \<rightarrow> q))\<close>
  using L3_17 L3_23 L3_25 L3_MP by metis

lemma L3_27: \<open>\<LL>\<^sub>3 (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  using L3_19 L3_26 L3_MP by metis

theorem L3_iff_L1: \<open>\<LL>\<^sub>3 p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have L1_L3_1: \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  have L1_L3_2: \<open>\<turnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  have L1_L3_3: \<open>\<turnstile> (((\<sim> p) \<rightarrow> (\<sim> q)) \<rightarrow> (q \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<LL>\<^sub>3 p\<close>
    using that by (induct) (metis MP, metis L1_L3_1, metis L1_L3_2, metis L1_L3_3)
  show \<open>\<LL>\<^sub>3 p\<close> if \<open>\<turnstile> p\<close>
    using that by (induct) (metis L3_MP, metis L3_14, metis L3_27, metis L3_9)
qed

theorem L3_soundness: \<open>\<LL>\<^sub>3 p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: L3.induct) auto

theorem L3_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<LL>\<^sub>3 p\<close>
  using L3_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<LL>\<^sub>3 p\<close>
  unfolding valid_def using L3_soundness L3_completeness by blast

lemmas L3 = L3.intros main

end
