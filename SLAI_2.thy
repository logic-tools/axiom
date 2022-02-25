(*
  Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory SLAI_2 imports System_L1 begin

text \<open>Inspired by Larry Wos: Conquering the Meredith Single Axiom, J. Autom. Reas. 27:175–199 2001\<close>

inductive Double (\<open>\<tturnstile>\<close>) where
  MP: \<open>\<tturnstile> q\<close> if \<open>\<tturnstile> p\<close> and \<open>\<tturnstile> (p \<rightarrow> q)\<close> |
  A1: \<open>\<tturnstile> (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (q \<rightarrow> r))\<close> |
  A2: \<open>\<tturnstile> ((\<sim> p \<rightarrow> (q \<rightarrow> \<sim> r)) \<rightarrow> ((p \<rightarrow> (q \<rightarrow> s)) \<rightarrow> ((r \<rightarrow> q) \<rightarrow> (r \<rightarrow> s))))\<close>

lemmas AX = A1 A2

lemma L1_1: \<open>\<tturnstile> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using AX MP by meson

lemma L1_2: \<open>\<tturnstile> ((\<sim> p \<rightarrow> p) \<rightarrow> p)\<close>
  using AX MP by metis

lemma L1_3: \<open>\<tturnstile> (p \<rightarrow> (\<sim> p \<rightarrow> q))\<close>
  using AX MP by metis

theorem \<open>\<turnstile> p \<longleftrightarrow> \<tturnstile> p\<close>
proof
  show \<open>\<turnstile> p\<close> if \<open>\<tturnstile> p\<close>
    using that by induct (use System_L1.MP in fast, use L1_completeness in simp_all)
  show \<open>\<tturnstile> p\<close> if \<open>\<turnstile> p\<close>
    using that by induct (use MP in fast, rule L1_1, rule L1_2, rule L1_3)
qed

end
