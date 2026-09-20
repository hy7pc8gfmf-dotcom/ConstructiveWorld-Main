(* ============================================================ *)
(* UpAblKVEpsHalf.v —— N6 席：KV 链 ε/2 分摊簿记普适化件（新独立件）     *)
(*   20260920                                                            *)
(* ============================================================ *)
(* 【使命】UpKVDrift_P2.v 442-448（kv_abs_triangle_list_eps 归纳 cons 臂）*)
(*   内联的 ε/2 分摊簿记三段实形——Hhalf 半量正性、Hinv2one inv(1+1)      *)
(*   倍元环账、Hhh 两半份重构 ε——普适化为可复用供给引理；接续 F1B 头注   *)
(*   第 3 条未竟项（字面 ε/2 簿记为后续席位增量点）。新独立件：           *)
(*   UpKVDrift_P2/UpAblAbsSumLeB 系与任何既有文件零触碰；KV 槽回接       *)
(*   Corollary 落本件内（原内联位点语句的等价重述形）。                   *)
(* 【普适化结构（keh_ 前缀，全库实扫零撞名）】                            *)
(*   0 局部代数包：keh_plus_zero_l / keh_one_mult_l / keh_distrib_r /     *)
(*     keh_two_pos / keh_self_two——基座只给左形，照 UpKVDrift_P2 既定    *)
(*     「各持一份同形定义」体例重建，本件仅依赖 CW_ConstructiveWorld_219。 *)
(*   1 普适供给引理（本件主增量）：                                       *)
(*     · keh_split_reconst：任意半量系数 c（c+c==1 即可，不问构造路线）   *)
(*       ⟹ (c·ε)+(c·ε)==ε——半量重构环账的系数参数化形（内联版为        *)
(*       inv(1+1) 专用特例）。                                            *)
(*     · keh_eps_half_amort：两点核差形 ε/2 前后分摊消费面普适引理——     *)
(*       三角余量 c·ε 与归纳余量 c·ε 两处半份，经重构环账合并为整 ε；    *)
(*       a b B 全称参量（内联位点仅 f w / Σ rest / Σ rest|f| 一处特例）。 *)
(*   2 规范半量供给包：keh_half := inv(1+1)（keh_two_pos 证书）＋        *)
(*     keh_half_pos / keh_half_double / keh_half_share_pos /              *)
(*     keh_half_share_reconst——442-448 三段内联的命名供给形。            *)
(*   3 KV 槽回接 Corollary：keh_kv_abs_triangle_list_eps——原内联位点     *)
(*     语句的等价重述形，cons 臂全程经 keh_eps_half_amort 供给，不再     *)
(*     内联簿记（UpKVDrift_P2 本体零触碰）。                              *)
(* 【诚实定性（红线三）】普适化增量＝①半量系数参数化（c+c==1 任证，       *)
(*   非 inv(1+1) 专用）、②消费面全称化（a b B 参量）、③供给面命名化      *)
(*   （可跨件复用）；回接 Corollary 语句面与 UpKVDrift_P2 原件同构，      *)
(*   非新数学语句，如实申报。                                             *)
(* 【红线自审】零承认件；纯构造性；语句面全 Set 层（real_eq/real_lt/     *)
(*   real_le），无裸命题层字面、无依和/合取编码；全部 Qed。               *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ---------- 0. 局部代数包（基座左形给足后的右形桥；照 UpKVDrift_P2 体例） ---------- *)

(* 0 + a == a（根内 real_plus_zero 只给 a + 0 == a） *)
Lemma keh_plus_zero_l : forall a : Real, real_eq (real_plus real_zero a) a.
Proof.
  intro a.
  exact (real_eq_trans (real_plus real_zero a) (real_plus a real_zero) a
           (real_plus_comm real_zero a) (real_plus_zero a)).
Qed.

(* 1·a == a（real_mult_one 为右形 a·1 == a 的左形桥） *)
Lemma keh_one_mult_l : forall a : Real, real_eq (real_mult real_one a) a.
Proof.
  intro a.
  exact (real_eq_trans (real_mult real_one a) (real_mult a real_one) a
           (real_mult_comm real_one a) (real_mult_one a)).
Qed.

(* 右分配：(a + b)·c == a·c + b·c（real_distrib 为左形；comm 桥） *)
Lemma keh_distrib_r : forall a b c0 : Real,
  real_eq (real_mult (real_plus a b) c0)
          (real_plus (real_mult a c0) (real_mult b c0)).
Proof.
  intros a b c0.
  apply (real_eq_trans (real_mult (real_plus a b) c0)
                       (real_mult c0 (real_plus a b)) _).
  - apply real_mult_comm.
  - apply (real_eq_trans (real_mult c0 (real_plus a b))
             (real_plus (real_mult c0 a) (real_mult c0 b)) _).
    + exact (real_distrib c0 a b).
    + apply (RealSetoid.real_eq_plus_compat (real_mult c0 a) (real_mult c0 b)
               (real_mult a c0) (real_mult b c0)
               (real_mult_comm c0 a) (real_mult_comm c0 b)).
Qed.

(* 2 = 1 + 1 > 0 *)
Lemma keh_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus real_one real_one)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_compat; exact real_lt_zero_one.
Qed.

(* t + t == (1+1)·t *)
Lemma keh_self_two : forall t : Real,
  real_eq (real_plus t t) (real_mult (real_plus real_one real_one) t).
Proof.
  intro t.
  apply (real_eq_trans
           (real_plus t t)
           (real_plus (real_mult t real_one) (real_mult t real_one))
           (real_mult (real_plus real_one real_one) t)).
  - apply (RealSetoid.real_eq_plus_compat t t (real_mult t real_one)
             (real_mult t real_one)
             (real_eq_sym (real_mult t real_one) t (real_mult_one t))
             (real_eq_sym (real_mult t real_one) t (real_mult_one t))).
  - apply (real_eq_trans
             (real_plus (real_mult t real_one) (real_mult t real_one))
             (real_plus (real_mult real_one t) (real_mult real_one t))
             (real_mult (real_plus real_one real_one) t)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult t real_one)
               (real_mult t real_one) (real_mult real_one t) (real_mult real_one t)
               (real_mult_comm t real_one) (real_mult_comm t real_one)).
    + exact (real_eq_sym _ _ (keh_distrib_r real_one real_one t)).
Qed.

(* ---------- 1. 普适供给引理（本件主增量） ---------- *)

(* 1a. 半量重构环账（系数参数化）：任取半量系数 c，只要 c + c == 1， *)
(*   则两半份 (c·ε)+(c·ε) 恰重构整 ε。内联版 Hhh 为 inv(1+1) 专用； *)
(*   此处对任意「倍元分解」证书开放（分配律＋倍元环账两步，与系数 *)
(*   构造路线无关）。 *)
Lemma keh_split_reconst : forall c eps : Real,
  real_eq (real_plus c c) real_one ->
  real_eq (real_plus (real_mult c eps) (real_mult c eps)) eps.
Proof.
  intros c eps Hcc.
  apply (real_eq_trans
           (real_plus (real_mult c eps) (real_mult c eps))
           (real_mult (real_plus c c) eps)
           eps).
  - apply real_eq_sym. apply keh_distrib_r.
  - apply (real_eq_trans
             (real_mult (real_plus c c) eps)
             (real_mult real_one eps)
             eps).
    + apply (RealSetoid.real_eq_mult_compat
               (real_plus c c) eps real_one eps
               Hcc (real_eq_refl eps)).
    + apply keh_one_mult_l.
Qed.

(* 1b. 半量正性传输：0 < c 且 0 < ε ⟹ 0 < c·ε *)
Lemma keh_split_pos : forall c eps : Real,
  real_lt real_zero c ->
  real_lt real_zero eps ->
  real_lt real_zero (real_mult c eps).
Proof.
  intros c eps Hc Heps. exact (real_mult_pos_compat c eps Hc Heps).
Qed.

(* 1c. 主供给引理·两点核差形 ε/2 前后分摊消费面： *)
(*   三角面给 |a+b| ≤ |a|+|b|+c·ε（前半份），归纳/下游面给 |b| ≤ B+c·ε *)
(*   （后半份），经 1a 重构环账两半份合并为整 ε。内联位点（UpKVDrift_P2 *)
(*   442-448）为本引理在 a:=f w、b:=Σrest、B:=Σrest|f|、c:=inv(1+1) 的 *)
(*   一次特例展开。 *)
Lemma keh_eps_half_amort : forall a b B c eps : Real,
  real_lt real_zero eps ->
  real_eq (real_plus c c) real_one ->
  real_lt real_zero c ->
  real_le (real_abs (real_plus a b))
          (real_plus (real_plus (real_abs a) (real_abs b)) (real_mult c eps)) ->
  real_le (real_abs b) (real_plus B (real_mult c eps)) ->
  real_le (real_abs (real_plus a b))
          (real_plus (real_plus (real_abs a) B) eps).
Proof.
  intros a b B c eps Heps Hcc Hc Htri Hib.
  apply (real_le_trans
           (real_abs (real_plus a b))
           (real_plus (real_plus (real_abs a) (real_abs b)) (real_mult c eps))
           (real_plus (real_plus (real_abs a) B) eps)
           Htri).
  apply (real_le_trans
           (real_plus (real_plus (real_abs a) (real_abs b)) (real_mult c eps))
           (real_plus
              (real_plus (real_abs a) (real_plus B (real_mult c eps)))
              (real_mult c eps))
           (real_plus (real_plus (real_abs a) B) eps)).
  - apply real_le_plus_compat.
    + apply real_le_plus_compat.
      * apply real_le_refl.
      * exact Hib.
    + apply real_le_refl.
  - apply (RealSetoid.real_eq_le _ _
             (real_eq_trans
                (real_plus
                   (real_plus (real_abs a) (real_plus B (real_mult c eps)))
                   (real_mult c eps))
                (real_plus
                   (real_plus (real_plus (real_abs a) B) (real_mult c eps))
                   (real_mult c eps))
                (real_plus (real_plus (real_abs a) B) eps)
                (RealSetoid.real_eq_plus_compat
                   (real_plus (real_abs a) (real_plus B (real_mult c eps)))
                   (real_mult c eps)
                   (real_plus (real_plus (real_abs a) B) (real_mult c eps))
                   (real_mult c eps)
                   (real_plus_assoc (real_abs a) B (real_mult c eps))
                   (real_eq_refl (real_mult c eps)))
                (real_eq_trans
                   (real_plus
                      (real_plus (real_plus (real_abs a) B) (real_mult c eps))
                      (real_mult c eps))
                   (real_plus
                      (real_plus (real_abs a) B)
                      (real_plus (real_mult c eps) (real_mult c eps)))
                   (real_plus (real_plus (real_abs a) B) eps)
                   (real_eq_sym _ _
                      (real_plus_assoc (real_plus (real_abs a) B)
                         (real_mult c eps) (real_mult c eps)))
                   (RealSetoid.real_eq_plus_compat
                      (real_plus (real_abs a) B)
                      (real_plus (real_mult c eps) (real_mult c eps))
                      (real_plus (real_abs a) B) eps
                      (real_eq_refl (real_plus (real_abs a) B))
                      (keh_split_reconst c eps Hcc))))).
Qed.

(* ---------- 2. 规范半量供给包（inv(1+1) 实例；442-448 内联实形的命名供给） ---------- *)

Definition keh_half : Real :=
  real_inv_pos (real_plus real_one real_one) keh_two_pos.

Lemma keh_half_pos : real_lt real_zero keh_half.
Proof.
  exact (real_inv_pos_pos (real_plus real_one real_one) keh_two_pos).
Qed.

(* inv(1+1) + inv(1+1) == 1（倍元环账：内联 Hinv2one 的命名形） *)
Lemma keh_half_double : real_eq (real_plus keh_half keh_half) real_one.
Proof.
  apply (real_eq_trans
           (real_plus keh_half keh_half)
           (real_mult (real_plus real_one real_one) keh_half)
           real_one).
  - exact (keh_self_two keh_half).
  - exact (real_inv_pos_correct (real_plus real_one real_one) keh_two_pos).
Qed.

Lemma keh_half_share_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (real_mult keh_half eps).
Proof.
  intros eps Heps. exact (keh_split_pos keh_half eps keh_half_pos Heps).
Qed.

Lemma keh_half_share_reconst : forall eps : Real,
  real_eq (real_plus (real_mult keh_half eps) (real_mult keh_half eps)) eps.
Proof.
  intros eps. exact (keh_split_reconst keh_half eps keh_half_double).
Qed.

(* ---------- 3. KV 槽回接 Corollary（原内联位点语句的等价重述形） ---------- *)

(* 语句面与 UpKVDrift_P2.kv_abs_triangle_list_eps 同构；cons 臂经 *)
(* keh_eps_half_amort＋规范半量包供给，簿记不再内联。 *)
Corollary keh_kv_abs_triangle_list_eps : forall (X : Set) (f : X -> Real)
  (l : list X) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l. induction l as [| w rest IH]; intros eps Heps.
  - apply (real_le_trans
             (real_abs (real_list_sum X f (@nil X))) real_zero
             (real_plus real_zero eps)).
    + apply RealSetoid.real_eq_le. exact real_abs_zero_req.
    + apply real_le_from_lt_aux.
      apply (RealSetoid.real_lt_id_r real_zero eps (real_plus real_zero eps)
               (real_eq_sym _ _ (keh_plus_zero_l eps)) Heps).
  - cbn [real_list_sum].
    apply (keh_eps_half_amort (f w) (real_list_sum X f rest)
             (real_list_sum X (fun x : X => real_abs (f x)) rest)
             keh_half eps Heps keh_half_double keh_half_pos).
    + exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest)
               (real_mult keh_half eps) (keh_half_share_pos eps Heps)).
    + exact (IH (real_mult keh_half eps) (keh_half_share_pos eps Heps)).
Qed.
