(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_F1 imports System_L3 begin

text \<open>System F from Gottlob Frege: Begriffsschrift (1879)\<close>

text \<open>Derivations are taken from: On Axiom Systems of Propositional Calculi. VII
                                  by Yoshinari Arai and Kiyoshi Iseki (1965)\<close>

inductive F (\<open>\<FF>\<close>) where
  F_MP: \<open>\<FF> q\<close> if \<open>\<FF> p\<close> and \<open>\<FF> (p \<rightarrow> q)\<close> |
  F_1:  \<open>\<FF> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  F_2:  \<open>\<FF> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close> |
  F_3:  \<open>\<FF> ((p \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> (\<sim> p)))\<close> |
  F_4:  \<open>\<FF> ((\<sim> (\<sim> p)) \<rightarrow> p)\<close> |
  F_5:  \<open>\<FF> (p \<rightarrow> (\<sim> (\<sim> p)))\<close>

lemma F_6: \<open>\<FF> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r))))\<close>
  using F_1 F_2 F_MP by metis

lemma F_7: \<open>\<FF> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using F_1 F_2 F_6 F_MP by metis

lemma F_8: \<open>\<FF> (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> q)))\<close>
  using F_1 F_MP by metis

lemma F_9: \<open>\<FF> (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> ((q \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r))))\<close>
  using F_7.

lemma F_10: \<open>\<FF> (((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using F_2 F_8 F_9 F_MP by metis

lemma F_11: \<open>\<FF> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close>
  using F_2 F_7 F_10 F_MP by metis

lemma F_12: \<open>\<FF> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using F_7 F_11 F_MP by metis

lemma F_13: \<open>\<FF> ((p \<rightarrow> (\<sim> q)) \<rightarrow> ((\<sim> (\<sim> q)) \<rightarrow> (\<sim> p)))\<close>
  using F_3.

lemma F_14: \<open>\<FF> (((\<sim> (\<sim> q)) \<rightarrow> (\<sim> p)) \<rightarrow> (q \<rightarrow> (\<sim> p)))\<close>
  using F_5 F_12 F_MP by metis

lemma F_15: \<open>\<FF> ((p \<rightarrow> (\<sim> q)) \<rightarrow> (q \<rightarrow> (\<sim> p)))\<close>
  using F_12 F_13 F_14 F_MP by metis

lemma F_16: \<open>\<FF> ((q \<rightarrow> (\<sim> (\<sim> p))) \<rightarrow> (q \<rightarrow> p))\<close>
  using F_4 F_7 F_MP by metis

lemma F_17: \<open>\<FF> (((\<sim> p) \<rightarrow> (\<sim> q)) \<rightarrow> (q \<rightarrow> p))\<close>
  using F_12 F_15 F_16 F_MP by metis

theorem F_iff_L3: \<open>\<FF> p \<longleftrightarrow> \<LL>\<^sub>3 p\<close>
proof
  have L3_F_3: \<open>\<LL>\<^sub>3 ((p \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> (\<sim> p)))\<close> for p q
    using L3_completeness by simp
  have L3_F_4: \<open>\<LL>\<^sub>3 ((\<sim> (\<sim> p)) \<rightarrow> p)\<close> for p
    using L3_completeness by simp
  have L3_F_5: \<open>\<LL>\<^sub>3 (p \<rightarrow> (\<sim> (\<sim> p)))\<close> for p
    using L3_completeness by simp
  show \<open>\<LL>\<^sub>3 p\<close> if \<open>\<FF> p\<close>
    using that by (induct) (metis L3_MP, metis L3_1, metis L3_2,
        metis L3_F_3, metis L3_F_4, metis L3_F_5)
  show \<open>\<FF> p\<close> if \<open>\<LL>\<^sub>3 p\<close>
    using that by (induct) (metis F_MP, metis F_1, metis F_2, metis F_17)
qed

theorem F_soundness: \<open>\<FF> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: F.induct) auto

theorem F_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<FF> p\<close>
  using F_iff_L3 by (simp add: L3_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<FF> p\<close>
  unfolding valid_def using F_soundness F_completeness by blast

lemmas F1 = F.intros main

end
