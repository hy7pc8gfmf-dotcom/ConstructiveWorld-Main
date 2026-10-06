(* ============================================================ *)
(* abl_loeb_d3_prf2.v — Formula2 凭证层第一段：Prf2 归纳系统 + gnPrf2 编码          *)
(*   （lbf_ 前缀；G10_LoebFam 库内 D3 空模块位第三段，接 abl_loeb_d3 与               *)
(*   abl_loeb_d3_ext）                                                          *)
(*                                                                *)
(*  使命: abl_loeb_d3_ext 的盒盲定理（lbe_verPf_f2_false / lbe_box_f2_false）           *)
(*   钉死的缺口：账本凭证空间只产出 Formula 码，有界可证性盒对 Formula2 句               *)
(*   恒假——全形提升缺的是 Formula2 自身的凭证层。本件补第一段：                          *)
(*   (1) Prf2：Formula2 的 Set 值归纳凭证系统，四条规则——                              *)
(*         prf2_lift（D1 账本整体嵌入：对一切 Formula g，Prf g 给出 Prf2 (f2b g)；       *)
(*               ax_eqT 的对应由 prf2_lift∘ax_eqT 承担），                              *)
(*         prf2_mp（分离规则的 fimp2 对应），                                            *)
(*         prf2_repl（值相等项代入的 fimp2 对应，evalF2_subst 语义承重）；                 *)
(*         prf2_sig（Σ-原子内化规则：真实账本行——g 有 Prf 凭证、其证明码在一切             *)
(*               赋值下低于界的取值、目标槽在一切赋值下读出 ⌜g⌝——升格为语言内               *)
(*               推理规则；G10_LoebFam 诚实边界 1 与 :3636-3639 接口建议 (b)              *)
(*               「账本升为语言内可证性谓词」的构造性落实。没有它，本系统对                 *)
(*               fsig 原子零可证，盒盲墙将以空可证性的形态原样存留）；                     *)
(*   (2) gnPrf2：Prf2 凭证码（标签 12–15）——项 0–3 / Formula 公式 4–5 / D1 证明          *)
(*         6–8 / Formula2 公式 9–11 / Prf2 凭证 12–15，四层码空间标签分区闭合；           *)
(*   (3) 凭证层首定理：lbf_Prf2_sound（Prf2 的元级可靠性，与 D1 Prf_soundness            *)
(*         同构；prf2_sig 肢把 G10 evalF2_fsig_ledger 使用为推理规则的可靠性）＋            *)
(*         码空间分区定理两件（D1 证明解码器 dP2 与 Formula2 解码器 lbe_dF2b             *)
(*         在任意充足燃料下拒绝一切 Prf2 码——新凭证码与旧两代码空间互斥的                 *)
(*         解码器侧表述）。                                                           *)
(*   对标行：G10_LoebFam :3631-3642 D3 接口建议 (a)(b)；abl_loeb_d3 :322 lbd_HBL1        *)
(*   （首定理形态的模板）；D1 Prf_soundness（G10 :719，可靠性定理形态的模板）。             *)
(*                                                                *)
(*  依赖: Require Import G10_LoebFam / abl_loeb_d3（lbd_dP2_norm）/            *)
(*   abl_loeb_d3_ext（lbe_gnF2 / lbe_dF2b / lbe_dF2b_norm）。                          *)
(*   编译配方: 先编供链 abl_loeb_d3.v → abl_loeb_d3_ext.v，再编本件：                              *)
(*   rocq c -native-compiler no -q -Q <池> "" -Q <vo_local 树> "" <件>.v                  *)
(*   （Rocq 9.1.0，工具链 Live/toolchain/opam/live；9.0.1 的 live901 因 vo 版本号           *)
(*   90100≠90001 不兼容。G10_LoebFam 从 vo_local_world_unified_0930 缓存 .vo               *)
(*   解析，池内不留其源码拷贝。）                                                     *)
(*                                                                *)
(* 【本件陈述（三段 10 件）】                                                        *)
(*   §A Prf2 归纳系统（四规则）+ lbf_Prf2_sound（凭证层首定理）；                        *)
(*   §B gnPrf2 编码（标签 12–15）+ lbf_lift_code_continuous（账本连续性：                  *)
(*       prf2_lift 码载荷逐字携带 D1 证明码）+ 码空间分区：                              *)
(*       lbf_dP2_S_gnPrf2_none / lbf_dP2_gnPrf2_none（D1 解码器拒绝 Prf2 码）；          *)
(*       lbf_dF2b_S_gnPrf2_none / lbf_dF2b_gnPrf2_none（F2 解码器拒绝 Prf2 码）；        *)
(*   §C 展品：lbf_demo_row（真实 D1 账本行 2624 < 3000 的 Σ-原子内化凭证，                  *)
(*       即 Prf2 (fsig (numT 3000) (numT ⌜teq 0 0⌝)) 的语言内证明项）+                    *)
(*       lbf_demo_row_sound / lbf_demo_code_dP2_blind 两实例。                           *)
(*                                                                *)
(* 【Set 载体纪律（构造性注记）】语句面零 Prop：Prf2 构造子前提位全部为 loeb_tid             *)
(*   载体（模板多态下 Set 值）的全称语句，与 D1 Prf 的 ax_eqT/repl 前提位同构；             *)
(*   存在以 sigT；界前提 (… ≤ …)%nat 为 Proof 层算术接口（与 D1 gnT_fuel、                *)
(*   D2 gnPrf_replay 接口同型）。零 Variable/Hypothesis/假设位；零公理、                  *)
(*   零承认、零占位、零经典逻辑；全链信息性，可提取。                                     *)
(*                                                                *)
(*  构造性: 全件 Set 载体零 Prop。诚实边界（fail-loud，同步登记于施工报告）：                                        *)
(*   本件不建 dPrf2 解码器/码级重演/MP2 封闭（后续工作），故 Formula2 上的                 *)
(*   有界可证性盒谓词本件不立；prf2_sig 的元级前提不入码（与 gnPrf 同形对应，              *)
(*   由 lbf_Prf2_sound 元级可靠性承担）；接口建议 (b) 的完备半边——元级前提的               *)
(*   码级证书化（闭项对 dT2 证书、(th,t1,t2) 证书三元组）与 prf2_sig 的                      *)
(*   界前提弱化——为后续山峰；无界搜索墙（rLPO 谱系）原样保留。                            *)
(*   禁拼凑：本件不以任何占位伪造解码器或盒谓词。                                        *)
(* ============================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Require Import G10_LoebFam.
Require Import abl_loeb_d3.
Require Import abl_loeb_d3_ext.

(* ===================================================================== *)
(* §A  Prf2：Formula2 的 Set 值归纳凭证系统（凭证层本体）                                 *)
(* ===================================================================== *)

(* 四条规则：D1 Prf 三构造子模式（ax/MP/Repl）的 F2 对应 + Σ 内化。
   prf2_sig 的两条前提与 G10 evalF2_fsig_ledger 的账本行前提逐字同形——
   账本行由此从元级前提升格为语言内推理规则。 *)
Inductive Prf2 : Formula2 -> Set :=
| prf2_lift : forall g : Formula, Prf g -> Prf2 (f2b g)
| prf2_mp : forall a b : Formula2, Prf2 (fimp2 a b) -> Prf2 a -> Prf2 b
| prf2_repl : forall (th : Formula2) (t1 t2 : Term),
    (forall s : nat -> nat, loeb_tid nat (valt t1 s) (valt t2 s)) ->
    Prf2 (fimp2 (substF2 th t1) (substF2 th t2))
| prf2_sig : forall (B c : Term) (g : Formula) (pf : Prf g),
    (forall s : nat -> nat, loeb_tid bool (Nat.ltb (gnPrf g pf) (valt B s)) true) ->
    (forall s : nat -> nat, loeb_tid nat (gnF g) (valt c s)) ->
    Prf2 (fsig B c).

(* ── 凭证层首定理（sound 首肢）：Prf2 的元级可靠性 ──
   与 D1 Prf_soundness（G10 :719）同构。prf2_lift 肢直接使用 D1 可靠性；
   prf2_sig 肢把 D2 的账本行定理 evalF2_fsig_ledger（G10 :3547）使用为
   推理规则的可靠性——Σ-原子的真从此有语言内凭证，不再只是元级记录。 *)
Theorem lbf_Prf2_sound : forall (f2 : Formula2) (pf : Prf2 f2) (s : nat -> nat),
  loeb_tid bool (evalF2 f2 s) true.
Proof.
  intros f2 pf. induction pf as
    [g pf0 | a b pf1 IH1 pf2 IH2 | th t1 t2 Hv | B c g pf0 Hb Hc]; intros s.
  - (* prf2_lift：D1 可靠性直接供账 *)
    cbn [evalF2]. exact (Prf_soundness g pf0 s).
  - (* prf2_mp：蕴含消去（fimp2 语义 = 布尔蕴含；与 D1 Prf_soundness mpF 肢同构：
       大前提的方程在小前提真值代入后化开，结论真值从中读出） *)
    tidQ (IH1 s) E1. tidQ (IH2 s) E2. cbn [evalF2] in E1. rewrite E2 in E1.
    cbn [negb orb] in E1. apply loeb_tid_eq. exact E1.
  - (* prf2_repl：代入不变量（evalF2_subst 两次改写 + 槽值恒等改写） *)
    cbn [evalF2]. rewrite (evalF2_subst th t1 s). rewrite (evalF2_subst th t2 s).
    tidQ (Hv s) E. rewrite E.
    apply loeb_tid_eq. destruct (evalF2 th (upd s (valt t2 s))); reflexivity.
  - (* prf2_sig：Σ-原子的账本行语义（evalF2_fsig_ledger 的推理规则化） *)
    exact (evalF2_fsig_ledger B c s g pf0 (Hb s) (Hc s)).
Qed.

(* ===================================================================== *)
(* §B  gnPrf2：Prf2 凭证码（标签 12–15）+ 码空间分区                                     *)
(* ===================================================================== *)

(* 凭证码：四标签 12–15 与项 0–3 / Formula 公式 4–5 / D1 证明 6–8 /
   Formula2 公式 9–11 互斥。prf2_sig 的码载荷存 (⌜B⌝, ⌜c⌝, ⌜g⌝, ⌜pf⌝) 四元组——
   解码器重演所需的全部码侧信息随行（元级前提照 D1 惯例不入码）。 *)
Fixpoint gnPrf2 (f2 : Formula2) (pf : Prf2 f2) {struct pf} : nat :=
  match pf in Prf2 f0 return nat with
  | @prf2_lift g pf0 => pairp 12 (gnPrf g pf0)
  | @prf2_mp a b pf1 pf2 => pairp 13 (pairp (gnPrf2 (fimp2 a b) pf1) (gnPrf2 a pf2))
  | @prf2_repl th t1 t2 _ => pairp 14 (pairp (pairp (lbe_gnF2 th) (gnT t1)) (gnT t2))
  | @prf2_sig B c g pf0 _ _ =>
      pairp 15 (pairp (pairp (gnT B) (gnT c)) (pairp (gnF g) (gnPrf g pf0)))
  end.

(* 账本连续性：prf2_lift 的码载荷逐字携带 D1 证明码——新凭证层的码空间里，
   D1 账本行以标签 12 原样居留（unp2_pair 一步读出）。 *)
Lemma lbf_lift_code_continuous : forall (g : Formula) (pf : Prf g),
  unp2 (gnPrf2 (f2b g) (prf2_lift g pf)) (gnPrf2 (f2b g) (prf2_lift g pf))
  = Some (12, gnPrf g pf).
Proof.
  intros g pf. cbn [gnPrf2]. apply unp2_pair.
Qed.

(* ── 码空间分区（解码器侧）：两张旧解码器拒绝一切 Prf2 码 ──
   技术要点沿 lbe_dF_gnF2_none 的两步法：自燃料形 dX2 (pairp …) (pairp …)
   的燃料非 constructor 头不可 iota 展开，先经燃料不变性抬到 S-燃料形
   （S-头可展），再 unp2_pair + 标签分派落通配枝。 *)

Lemma lbf_dP2_S_gnPrf2_none : forall (f2 : Formula2) (pf : Prf2 f2),
  dP2 (Datatypes.S (gnPrf2 f2 pf)) (gnPrf2 f2 pf) = None.
Proof.
  intros f2 pf.
  destruct pf as [g pf0 | a b pf1 pf2 | th t1 t2 Hv | B c g pf0 Hb Hc];
    cbn [gnPrf2 dP2]; rewrite unp2_pair; cbv iota; reflexivity.
Qed.

(* D1 证明解码器在任意充足燃料下拒绝 Prf2 码（使用 abl_loeb_d3 lbd_dP2_norm） *)
Theorem lbf_dP2_gnPrf2_none : forall (f2 : Formula2) (pf : Prf2 f2) (k : nat),
  (gnPrf2 f2 pf <= k)%nat -> dP2 k (gnPrf2 f2 pf) = None.
Proof.
  intros f2 pf k Hk.
  rewrite (lbd_dP2_norm (gnPrf2 f2 pf) k Hk).
  rewrite <- (lbd_dP2_norm (gnPrf2 f2 pf) (Datatypes.S (gnPrf2 f2 pf))
               (Nat.le_succ_diag_r _)).
  apply lbf_dP2_S_gnPrf2_none.
Qed.

Lemma lbf_dF2b_S_gnPrf2_none : forall (f2 : Formula2) (pf : Prf2 f2),
  lbe_dF2b (Datatypes.S (gnPrf2 f2 pf)) (gnPrf2 f2 pf) = None.
Proof.
  intros f2 pf.
  destruct pf as [g pf0 | a b pf1 pf2 | th t1 t2 Hv | B c g pf0 Hb Hc];
    cbn [gnPrf2 lbe_dF2b]; rewrite unp2_pair; cbv iota; reflexivity.
Qed.

(* Formula2 公式解码器在任意充足燃料下拒绝 Prf2 码（使用 abl_loeb_d3_ext
   lbe_dF2b_norm） *)
Theorem lbf_dF2b_gnPrf2_none : forall (f2 : Formula2) (pf : Prf2 f2) (k : nat),
  (gnPrf2 f2 pf <= k)%nat -> lbe_dF2b k (gnPrf2 f2 pf) = None.
Proof.
  intros f2 pf k Hk.
  rewrite (lbe_dF2b_norm (gnPrf2 f2 pf) k Hk).
  rewrite <- (lbe_dF2b_norm (gnPrf2 f2 pf) (Datatypes.S (gnPrf2 f2 pf))
               (Nat.le_succ_diag_r _)).
  apply lbf_dF2b_S_gnPrf2_none.
Qed.

(* ===================================================================== *)
(* §C  展品：第一张 Σ-原子内化凭证（真实 D1 账本行 2624 < 3000 的语言内升格）                *)
(* ===================================================================== *)

Definition lbf_demo_pf0 : Prf (teq tzero tzero) :=
  ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)).

(* 账本行低于界：证明码在一切赋值下低于界的取值（numT 3000 为闭项，取值恒 3000） *)
Lemma lbf_demo_row_below : forall s : nat -> nat,
  loeb_tid bool
    (Nat.ltb (gnPrf (teq tzero tzero) lbf_demo_pf0) (valt (numT 3000) s)) true.
Proof.
  intros s. apply loeb_tid_eq. rewrite valt_numT.
  apply (proj2 (Nat.ltb_lt (gnPrf (teq tzero tzero) lbf_demo_pf0) 3000)).
  vm_compute. lia.
Qed.

Definition lbf_demo_atom : Formula2 :=
  fsig (numT 3000) (numT (gnF (teq tzero tzero))).

(* 第一张内化凭证：D1 证明码 2624 的账本行，经 prf2_sig 升格为
   Prf2 (fsig (numT 3000) (numT ⌜teq 0 0⌝)) 的语言内证明项——
   D2 的 Σ(σ) 桥接展示（G10 Sigma_atom_fires_via_ledger）由此获得
   一等凭证形态。 *)
Definition lbf_demo_row : Prf2 lbf_demo_atom :=
  prf2_sig (numT 3000) (numT (gnF (teq tzero tzero))) (teq tzero tzero)
    lbf_demo_pf0 lbf_demo_row_below
    (fun s : nat -> nat => loeb_tid_refl nat (gnF (teq tzero tzero))).

(* 展品一：凭证的元级可靠性（lbf_Prf2_sound 实例——Σ-原子在平凡赋值下为真） *)
Theorem lbf_demo_row_sound :
  loeb_tid bool (evalF2 lbf_demo_atom (fun _ : nat => 0)) true.
Proof. exact (lbf_Prf2_sound lbf_demo_atom lbf_demo_row (fun _ : nat => 0)). Qed.

(* 展品二：新凭证码对 D1 解码器不可见（码空间分区定理实例——D1 账本的
   搜索空间里没有本凭证码的伪证） *)
Theorem lbf_demo_code_dP2_blind : forall k : nat,
  (gnPrf2 lbf_demo_atom lbf_demo_row <= k)%nat ->
  dP2 k (gnPrf2 lbf_demo_atom lbf_demo_row) = None.
Proof. exact (lbf_dP2_gnPrf2_none lbf_demo_atom lbf_demo_row). Qed.

(* —— 假设面自审（全部应 Closed under the global context） —— *)
Print Assumptions lbf_Prf2_sound.
Print Assumptions gnPrf2.
Print Assumptions lbf_lift_code_continuous.
Print Assumptions lbf_dP2_gnPrf2_none.
Print Assumptions lbf_dF2b_gnPrf2_none.
Print Assumptions lbf_demo_row_sound.
Print Assumptions lbf_demo_code_dP2_blind.
