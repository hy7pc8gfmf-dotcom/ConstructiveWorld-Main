(* ============================================================
   piu1932_tight_bound_instantiated.v —— 幂率型紧上界的实例化收尾
   数学使命: 幂率距离证书族到位后,一致型紧上界的实例化交付——定义幂率
   深度型 kernel margin 族 ck_α(C0,α,q) := C0/h(q)^α (h := lw1m_height),
   以 π 分离闭式证书链(eps2 链闭式钉定形)驱动逐 q 率族 c(q)/3·h(q)^{-α},
   经 margin 换形(正数域率族/非正数域 ck_α 分片)填充一致型收尾件的证书
   前提位四支(HC0_pos/Hcrt_pos/Hcrt_dist/Hcert_pow),其上 l2_escape
   实例化与 antitone/Q 算术收尾机械跟随:换基搜索停点 ≤ 幂率深度选窗级
   S(tlw1703_unif_bpow_c C0 α h) = S(S(⌈(8/C0)·h^α⌉))(后继加一形)。
   一致常数支配位居显式前提位(条件式):该位即有效 μ(π) ≤ α 证书链本体,
   证书链到位则全链闭合,如实按接口位承载。
   依赖清单: Stdlib QArith/Qabs/Qround/Bool/Arith/Lia/List(Qring);
   S01_BaseRing;S02_CauchyComplete;S03_QExp;PiEnvelope;LW0LeibWindow;
   LW5SepComplexity;LW1PiMeasure;tlw1448_rebase/transfer/l2escape;
   piu1901_leibsep_q_kernel_closed;piu1904_mu2_certificate;
   tlw1703_unif_tight_instantiation(条件式一致型收尾件)。
   对标行: tlw1703_unif_tight_instantiation :44-57/:60/:84/:155/:175;
   piu1904_mu2_certificate :60/:87;LW1PiMeasure :48/:174/:180;
   tlw1448_transfer :60/:67;LW0LeibSeparation leibsep_q_kernel(全域核)。
   构造性注记: 全 Set/Type 层;零公理零承认;前提位填充为供件实例化
   (闭式证书链逐字同形换形),非承认式;见证级形态如实承载——逐 q 证书取
   projT1 包络项(非可计算字面),一致常数支配位居显式前提位(条件式);
   分片定义经 Qlt_le_dec 判定和(sumbool 可计算);结论位承载于 NatLe;
   Q 线性算术辅助步以 lia 承担(例外册在册用法·于此申报),主定理收尾为
   供件装配链非求解器。
   编译配方: coqc -native-compiler no -q -Q〈认证 vo 树目录〉""
   -Q〈本件目录〉"" piu1932_tight_bound_instantiated.v (COQLIB/ROCQLIB
   全字面双 export;cpu_guard v3 包裹)
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround Bool.Bool Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Qring.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import PiEnvelope.
Require Import LW0LeibWindow.
Require Import LW5SepComplexity.
Require Import LW1PiMeasure.
Require Import tlw1448_rebase.
Require Import tlw1448_transfer.
Require Import tlw1448_l2escape.
Require Import piu1901_leibsep_q_kernel_closed.
Require Import piu1904_mu2_certificate.
Require Import tlw1703_unif_tight_instantiation.

(* —— 幂率深度型 kernel margin 族 ck_α —— *)
Definition piu1932_ck_alpha (C0 : Q) (alpha : nat) (q : Q) : Q :=
  (C0 / q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) alpha)%Q.

(* —— 证书率族:全域分片(正数域=闭式链率族,非正数域=ck_α 自身) —— *)
Definition piu1932_crt (C0 : Q) (alpha : nat) (q : Q) : Q :=
  match Qlt_le_dec 0 q with
  | left Hpos =>
      ((piu1904_cwin_of q (Qlt_to_QltT 0 q Hpos) * (1 # 3))%Q
        / (Z.of_nat (lw1m_hpow q alpha) # 1)%Q)%Q
  | right _ => piu1932_ck_alpha C0 alpha q
  end.

(* QleT' 自反与 Qle → QleT' 桥(Qle_bool_iff 正向:序前提给判定和真支) *)
Lemma piu1932_qleT'_refl : forall x : Q, QleT' x x.
Proof.
  intros x. unfold QleT'.
  assert (Hb : Qle_bool x x = true).
  { apply (proj2 (Qle_bool_iff x x)). exact (Qle_refl x). }
  rewrite Hb. apply id_refl.
Qed.

Lemma piu1932_qle_to_qleT' : forall x y : Q, Qle x y -> QleT' x y.
Proof.
  intros x y H. unfold QleT'.
  assert (Hb : Qle_bool x y = true).
  { apply (proj2 (Qle_bool_iff x y)). exact H. }
  rewrite Hb. apply id_refl.
Qed.

(* 除法正性:分子严格正 × 分母非负严格(先乘后逆的 Q 算术链) *)
Lemma piu1932_div_pos : forall x y : Q, Qlt 0 x -> QltT' 0 y -> QltT' 0 (x / y)%Q.
Proof.
  intros x y Hx Hy. apply Qlt_to_QltT'. unfold Qdiv.
  apply (Qmult_lt_0_compat x (Qinv y)).
  - exact Hx.
  - apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ Hy).
Qed.

Section Piu1932Instantiation.

Variable C0 : Q.          (* 一致常数(margin 常数位) *)
Variable alpha : nat.     (* 幂率指数 *)

(* —— 诚实接口位(Set 承载·显式前提披露)——
   ①常数正性;②非正数域距离面(ck_α 点位);③正数域幂率支配:ck_α ≤
   闭式链率族 c(q)/3·h(q)^{-α}(率族以分支显形·见证参数全称化),
   即「有效 μ(π) ≤ α」证书链的到位位。 *)
Hypothesis HC0_pos : QltT' 0 C0.
Hypothesis Hnp_dist : forall q : Q,
  QleT' q 0 -> lw1m_dist_pt q (piu1932_ck_alpha C0 alpha q).
Hypothesis HC0_valid : forall (q : Q) (Hpos : (0 < q)%Q),
  QleT' (piu1932_ck_alpha C0 alpha q)
    ((piu1904_cwin_of q (Qlt_to_QltT 0 q Hpos) * (1 # 3))%Q
      / (Z.of_nat (lw1m_hpow q alpha) # 1)%Q)%Q.

(* 前提位一(正性):正数域取闭式窗见证正性 × 1/3 × h^α,非正数域取
   C0 正性 × q_pow 正性 *)
Lemma piu1932_crt_pos : forall q : Q, QltT' 0 (piu1932_crt C0 alpha q).
Proof.
  intros q. unfold piu1932_crt.
  destruct (Qlt_le_dec 0 q) as [Hpos | Hneg].
  - assert (Hcw : QltT 0 (piu1904_cwin_of q (Qlt_to_QltT 0 q Hpos))).
    { unfold piu1904_cwin_of.
      exact (fst (projT2 (leibsep_q_kernel_closed_window q (Qlt_to_QltT 0 q Hpos)))). }
    assert (H3 : Qlt 0 ((piu1904_cwin_of q (Qlt_to_QltT 0 q Hpos) * (1 # 3))%Q)).
    { apply (Qmult_lt_0_compat _ _).
      - exact (QltT_to_Qlt _ _ Hcw).
      - unfold Qlt. cbn [Qnum Qden]. lia. }
    apply piu1932_div_pos.
    + exact H3.
    + apply lw1m_hpowQ_pos.
  - apply piu1932_div_pos.
    + exact (QltT_to_Qlt _ _ HC0_pos).
    + apply Qlt_to_QltT'. apply tlw1703_unif_qpow_pos.
      exact (QltT_to_Qlt _ _ (lw1m_snq_pos (Pos.to_nat (Qden (Qred q))))).
Qed.

(* 前提位二(逐点距离):正数域取闭式链距离率面(逐字同形),非正数域取
   接口位② *)
Lemma piu1932_crt_dist : forall q : Q, lw1m_dist_pt q (piu1932_crt C0 alpha q).
Proof.
  intros q. unfold piu1932_crt.
  destruct (Qlt_le_dec 0 q) as [Hpos | Hneg].
  - exact (piu1904_dist_closed q alpha (Qlt_to_QltT 0 q Hpos)).
  - apply (Hnp_dist q). apply piu1932_qle_to_qleT'. exact Hneg.
Qed.

(* 前提位三(幂率支配·margin 换形):正数域取接口位③,非正数域自反 *)
Lemma piu1932_ck_alpha_le_crt : forall q : Q,
  QleT' (piu1932_ck_alpha C0 alpha q) (piu1932_crt C0 alpha q).
Proof.
  intros q. unfold piu1932_crt.
  destruct (Qlt_le_dec 0 q) as [Hpos | Hneg].
  - exact (HC0_valid q Hpos).
  - apply piu1932_qleT'_refl.
Qed.

(** 主定理一(l2_escape 实例化):换基搜索停点不超过换形余量的
    S(pie_modulus(·/2)) 窗级——一致型收尾件在填充后的证书族上实例化。 *)
Theorem piu1932_stop_le_ckwin : forall q : Q,
  NatLe (tlw1448_nsep_rebase tlw1448_ck q)
        (Datatypes.S (pie_modulus (piu1932_crt C0 alpha q / 2)%Q)).
Proof.
  exact (tlw1703_unif_tight_instantiation (piu1932_crt C0 alpha)
           piu1932_crt_pos piu1932_crt_dist).
Qed.

(** 换算支(antitone/Q 算术):余量窗阶受幂率换算界支配——一致型模量
    引理在填充后的证书族上实例化。 *)
Lemma piu1932_ckwin_le_bpow : forall q : Q,
  (pie_modulus (piu1932_crt C0 alpha q / 2)%Q
     <= tlw1703_unif_bpow_c C0 alpha (lw1m_height q))%nat.
Proof.
  exact (tlw1703_unif_modulus_le C0 alpha (piu1932_crt C0 alpha)
           HC0_pos piu1932_crt_pos piu1932_ck_alpha_le_crt).
Qed.

(** 主定理二(紧上界合成):换基搜索停点 ≤ 幂率深度选窗级——主定理一
    与换算支经后继单调性合成,展开即 S(S(⌈(8/C0)·h^α⌉)) 形。 *)
Theorem piu1932_stop_le_bpow : forall q : Q,
  NatLe (tlw1448_nsep_rebase tlw1448_ck q)
        (Datatypes.S (tlw1703_unif_bpow_c C0 alpha (lw1m_height q))).
Proof.
  intros q.
  apply NatLe_lift.
  apply Nat.le_trans with (m := Datatypes.S (pie_modulus (piu1932_crt C0 alpha q / 2)%Q)).
  - apply NatLe_drop. exact (piu1932_stop_le_ckwin q).
  - apply le_n_S. exact (piu1932_ckwin_le_bpow q).
Qed.

End Piu1932Instantiation.

(* ---- 假设审计(应全 Closed:前提位已随 Section 关闭转入语句前提位)---- *)
Print Assumptions piu1932_qleT'_refl.
Print Assumptions piu1932_qle_to_qleT'.
Print Assumptions piu1932_div_pos.
Print Assumptions piu1932_crt_pos.
Print Assumptions piu1932_crt_dist.
Print Assumptions piu1932_ck_alpha_le_crt.
Print Assumptions piu1932_stop_le_ckwin.
Print Assumptions piu1932_ckwin_le_bpow.
Print Assumptions piu1932_stop_le_bpow.

(* ---- 提取检验(计算面:ck_α 与证书率族)---- *)
Separate Extraction piu1932_ck_alpha piu1932_crt.
