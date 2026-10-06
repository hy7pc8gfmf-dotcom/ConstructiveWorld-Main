(* ============================================================ *)
(* abl_loeb_d3.v — Löb 主定理 D3·本切片：HBL 导出条件的                     *)
(*   构造性形式化（lbd_ 前缀，G10_LoebFam 库内 D3 空模块位第一段）                  *)
(*                                                                *)
(*  使命: G10_LoebFam.v :870 内联路标「D3 导出条件建议：D1' = Prf f → 账本(⌜f⌝)   *)
(*   居留；D2' = MP 的码级封闭；D3' = 编码自涉」的落地第一段：以 D2 已建的             *)
(*   verPf/bsearch/MPc/gnPrf 为地基，把语言内可证性谓词升为一等 bool 谓词             *)
(*   lbd_Box（= Formula2 的 fsig Σ-原子在平凡赋值下的取值），并在其上逐肢             *)
(*   构造性证明 Hilbert–Bernays–Löb 三导出条件。                                    *)
(*                                                                *)
(*  依赖: Require Import G10_LoebFam（本池同名拷贝留档；其 .vo 使用        *)
(*   vo_local_world_unified_0930 新鲜树，md5 与 Live 源一致 51bb7b3e）。            *)
(*   编译配方: rocq c -native-compiler no -q -Q <池> "" -Q <vo_local 树> "" abl_loeb_d3.v      *)
(*   （Rocq 9.1.0，工具链 Live/toolchain/opam/live；9.0.1 的 live901 因 vo 版本号       *)
(*   90100≠90001 不兼容，误用即报 bad version number。）                          *)
(*                                                                *)
(* 【本件陈述（四段 15 件）】                                                      *)
(*   §A 解码器燃料不变性（新定理，D1/D2 缺件）：                                    *)
(*     lbd_unp2_self_bounds（unp2 自燃料分解的分量界：第一分量 ≤ 码、第二分量 < 码）  *)
(*     lbd_dT2_fuel_inv / lbd_dF2_fuel_inv / lbd_dP2_fuel_inv                       *)
(*       （三解码器对燃料不敏感：c ≤ k1 ∧ c ≤ k2 → dX2 k1 c = dX2 k2 c——               *)
(*        解码的是码而非燃料，燃料只是递归护栏；D1 的 gnT_fuel/gnF_fuel 与             *)
(*        D2 的 gnPrf_replay 只给「码侧充足燃料」单向，本件补双向不变性）；            *)
(*     lbd_dP2_norm（自燃料规范化推论）。                                          *)
(*   §B 码序三件：lbd_pairp_gt_snd / lbd_pairp_mono / lbd_pairp_mono_snd_lt           *)
(*       （配对函数的严格/非严格单调，界迁移的算术承重）。                            *)
(*   §C HBL 三导出条件（层 1 主目标）：                                             *)
(*     lbd_Box B c := bsearch B (fun w => verPf w c)——有界可证性谓词，                *)
(*       且 lbd_Box_lang_internal 钉死其语言内身份（= fsig Σ-原子取值）；             *)
(*     lbd_mpT（MP 码级传递子 = MPc 有序实例）、lbd_boxup（MP 合成的界闭包映射）；      *)
(*     lbd_replay_upgrade（bool 证书 → 重演账升格：verPf w c = true 给出               *)
(*       显式公式 g 使 dP2 w w = Some g 且 ⌜g⌝ = c——Σ 反射半边的构造性补全）；         *)
(*     lbd_replay_uniform（升格后的一致燃料重演，燃料参数化定理形）；                  *)
(*     lbd_HBL1（必然化：⊢f 则 □_B⌜f⌝ 于显式界真）；                                 *)
(*     lbd_HBL3（K 形：□_B⌜f→g⌝ → □_B⌜f⌝ → □_{boxup B}⌜g⌝——界显式迁移）；            *)
(*     lbd_HBL2（规则形：⊢f→g 则 □_B⌜f⌝ → □_{boxup(pairp (S cB) B)}⌜g⌝）。            *)
(*   §D D3' 编码自涉展品（层 2）：                                                  *)
(*     lbd_diag_necessitation：对任一元 th，对角句 d=diagF th 的 Löb 蕴含               *)
(*       (th(⌜d⌝)→d) 的盒在「由其证明码直接算出」的界 lbd_boxup(⌜凭证⌝) 处为真——          *)
(*       守卫是构造性的：界不是存在假设而是闭式计算。                                 *)
(*                                                                *)
(*  构造性: Set 载体纪律，语句面零 Prop：存在以 sigT、合取以 prod、等式以 loeb_tid/bool 方程、    *)
(*   序以 (… ≤ …)%nat 界前提（燃料参数化形，与 D1 gnT_fuel/D2 gnPrf_replay 接口          *)
(*   完全同型——Proof 层算术接口，非 Set 层数据）。零公理、零承认、零占位、               *)
(*   零经典逻辑；全链信息性，可提取。                                               *)
(*                                                                *)
(* 【fail-loud 记录（层 2/层 3 诚实边界，同步登记于施工报告】）                          *)
(*   全形 Löb 本切片不闭合，精确障碍两点：                                          *)
(*   (i) 对象语言缺 □ 构造子：Formula 仅 teq/fimp，□ 句须为 Formula2 的 fsig 原子；      *)
(*       固定点 x ↦ fimp2 (fsig B x) p 的对角机制需 Formula2 自身的哥德尔编码              *)
(*       gnF2/dF2b 往返（标签 9/10/11）——G10_LoebFam :3633 接口建议原文，                  *)
(*       是下一切片的既知山峰。                                                    *)
(*   (ii) 无界搜索墙（rLPO 谱系）：无守卫 □（去掉界 B）须对任意码判定 verPf，             *)
(*       即 unbounded bsearch——库内 bsearch 是结构递归有界搜索，无界化即经典原理。        *)
(*       有守卫形态（界随证明码闭式迁移）本件已闭合，降档命名 guarded。                   *)
(*   禁拼凑：本件不以任何占位/循环假设伪造 □(□f→f)→f 形语句。                            *)
(* ============================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.

Require Import G10_LoebFam.

(* ===================================================================== *)
(* §A  解码器燃料不变性：解码的是码，燃料只是递归护栏                              *)
(*     D1 的 gnT_fuel/gnF_fuel 与 D2 的 gnPrf_replay 给的都是「码侧充足燃料」        *)
(*     单向（gnX ≤ k → dX2 k (gnX) = Some …）；本段补任意码的双向不变性，              *)
(*     是 verPf bool 证书升格为一致燃料重演账的承重件。                              *)
(* ===================================================================== *)

(* unp2 自燃料分解的分量界：第一分量 ≤ 码、第二分量严格 < 码 *)
Lemma lbd_unp2_self_bounds : forall x a b : nat,
  unp2 x x = Some (a, b) ->
  (a <= x)%nat /\ (b <= x)%nat /\ (b < x)%nat.
Proof.
  intros x. induction x as [x IH] using lt_wf_ind. intros a b H.
  destruct x as [|x'].
  - discriminate H.
  - rewrite (unp2_S x' (Datatypes.S x')) in H. cbv iota in H.
    destruct (Nat.even (Datatypes.S x')) eqn:Ev.
    + destruct (unp2 x' (Nat.div2 (Datatypes.S x'))) as [[a0 b0]|] eqn:Eq.
      * injection H as Ha Hb.
        pose proof (Nat.le_div2 x') as Hd.
        pose proof (unp2_fuel (Nat.div2 (Datatypes.S x')) x' Hd) as Hfuel.
        rewrite Hfuel in Eq.
        assert (Hlt : (Nat.div2 (Datatypes.S x') < Datatypes.S x')%nat) by lia.
        destruct (IH (Nat.div2 (Datatypes.S x')) Hlt a0 b0 Eq) as [Ha1 [Hb1 Hb2]].
        rewrite <- Ha, <- Hb. repeat split; lia.
      * discriminate H.
    + injection H as Ha Hb.
      pose proof (div2_le x') as Hd.
      rewrite <- Ha, <- Hb. repeat split; lia.
Qed.

(* dT2 燃料不变性 *)
Lemma lbd_dT2_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> dT2 k1 c = dT2 k2 c.
Proof.
  intros c. induction c as [c IH] using lt_wf_ind. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [dT2].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota. destruct l as [|[|[|[|l3]]]]; cbv iota; try reflexivity.
      * (* 标签 2：tsucc，子码 q 是第二分量，严格低于码 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S O)) q Epc) as Hb.
        destruct Hb as [_ [Hq Hlt]].
        assert (Ha1 : (q <= k1')%nat) by lia.
        assert (Ha2 : (q <= k2')%nat) by lia.
        rewrite (IH q Hlt k1' k2' Ha1 Ha2). reflexivity.
      * (* 标签 3：tsub，两子码 a b 低于 q < 码 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S O))) q Epc) as Hb1.
        destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b Epq) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        assert (Ha1 : (a <= k1')%nat) by lia.
        assert (Ha2 : (a <= k2')%nat) by lia.
        assert (Hb1 : (b <= k1')%nat) by lia.
        assert (Hb2 : (b <= k2')%nat) by lia.
        assert (Hla : (a < Datatypes.S c')%nat) by lia.
        assert (Hlb : (b < Datatypes.S c')%nat) by lia.
        rewrite (IH a Hla k1' k2' Ha1 Ha2). rewrite (IH b Hlb k1' k2' Hb1 Hb2).
        reflexivity.
    + reflexivity.
Qed.

(* dF2 燃料不变性（使用 dT2 不变性；自身沿码强归纳） *)
Lemma lbd_dF2_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> dF2 k1 c = dF2 k2 c.
Proof.
  intros c. induction c as [c IH] using lt_wf_ind. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [dF2].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota. destruct l as [|[|[|[|[|[|l3]]]]]]; cbv iota; try reflexivity.
      * (* 标签 4：teq，dT2 两路 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))) q Epc)
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b Epq) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        assert (Hta : dT2 k1' a = dT2 k2' a) by (apply lbd_dT2_fuel_inv; lia).
        assert (Htb : dT2 k1' b = dT2 k2' b) by (apply lbd_dT2_fuel_inv; lia).
        rewrite Hta, Htb. reflexivity.
      * (* 标签 5：fimp，dF2 两路（自身 IH） *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))) q Epc)
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b Epq) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        assert (Ha1 : (a <= k1')%nat) by lia.
        assert (Ha2 : (a <= k2')%nat) by lia.
        assert (Hb1 : (b <= k1')%nat) by lia.
        assert (Hb2 : (b <= k2')%nat) by lia.
        assert (Hla : (a < Datatypes.S c')%nat) by lia.
        assert (Hlb : (b < Datatypes.S c')%nat) by lia.
        rewrite (IH a Hla k1' k2' Ha1 Ha2). rewrite (IH b Hlb k1' k2' Hb1 Hb2).
        reflexivity.
    + reflexivity.
Qed.

(* dP2 燃料不变性（使用 dT2/dF2 不变性；自身沿码强归纳） *)
Lemma lbd_dP2_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> dP2 k1 c = dP2 k2 c.
Proof.
  intros c. induction c as [c IH] using lt_wf_ind. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [dP2].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota.
      destruct l as [|[|[|[|[|[|[|[|[|l3]]]]]]]]]; cbv iota; try reflexivity.
      * (* 标签 6：ax_eqT，dT2 两路 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))) q Epc)
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q a b Epq) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        assert (Hta : dT2 k1' a = dT2 k2' a) by (apply lbd_dT2_fuel_inv; lia).
        assert (Htb : dT2 k1' b = dT2 k2' b) by (apply lbd_dT2_fuel_inv; lia).
        rewrite Hta, Htb. reflexivity.
      * (* 标签 7：mpF，两子凭证码沿 dP2 自身不变性 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))) q Epc)
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[w1 w2]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q w1 w2 Epq) as Hb2.
        destruct Hb2 as [Hw1 [Hw2 Hw2lt]].
        assert (Hu1 : (w1 <= k1')%nat) by lia.
        assert (Hu2 : (w1 <= k2')%nat) by lia.
        assert (Hv1 : (w2 <= k1')%nat) by lia.
        assert (Hv2 : (w2 <= k2')%nat) by lia.
        assert (Hl1 : (w1 < Datatypes.S c')%nat) by lia.
        assert (Hl2 : (w2 < Datatypes.S c')%nat) by lia.
        rewrite (IH w1 Hl1 k1' k2' Hu1 Hu2). rewrite (IH w2 Hl2 k1' k2' Hv1 Hv2).
        reflexivity.
      * (* 标签 8：repl，dF2 一路 dT2 两路 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))))) q Epc)
          as Hb1. destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[p0 r]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q p0 r Epq) as Hb2.
        destruct Hb2 as [Hp [Hr Hrlt]].
        destruct (unp2 p0 p0) as [[a b]|] eqn:Epp; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds p0 a b Epp) as Hb3.
        destruct Hb3 as [Hpa [Hpb _]].
        assert (Hfa1 : (a <= k1')%nat) by lia.
        assert (Hfa2 : (a <= k2')%nat) by lia.
        assert (Hfa : dF2 k1' a = dF2 k2' a) by (apply lbd_dF2_fuel_inv; lia).
        assert (Htb : dT2 k1' b = dT2 k2' b) by (apply lbd_dT2_fuel_inv; lia).
        assert (Htr : dT2 k1' r = dT2 k2' r) by (apply lbd_dT2_fuel_inv; lia).
        rewrite Hfa, Htb, Htr. reflexivity.
    + reflexivity.
Qed.

(* 自燃料规范化推论：充足燃料下与自燃料一致（D1 unp2_fuel 的 dP2 版） *)
Corollary lbd_dP2_norm : forall c k : nat, (c <= k)%nat -> dP2 k c = dP2 c c.
Proof.
  intros c k H. apply (lbd_dP2_fuel_inv c k c); [exact H | apply Nat.le_refl].
Qed.

(* ===================================================================== *)
(* §B  码序三件：配对函数的单调性（界迁移的算术承重）                                *)
(* ===================================================================== *)

Lemma lbd_pairp_gt_snd : forall a b : nat, (b < pairp a b)%nat.
Proof.
  induction a as [|a IHa]; intros b; cbn [pairp].
  - lia.
  - specialize (IHa b). lia.
Qed.

Lemma lbd_pairp_mono : forall a a' b b' : nat,
  (a <= a')%nat -> (b <= b')%nat -> (pairp a b <= pairp a' b')%nat.
Proof.
  intros a. induction a as [|a IHa]; intros a' b b' Ha Hb.
  - destruct a' as [|a''].
    + cbn [pairp]. lia.
    + cbn [pairp]. pose proof (lbd_pairp_gt_snd a'' b'). lia.
  - destruct a' as [|a''].
    + lia.
    + cbn [pairp]. assert (Ha2 : (a <= a'')%nat) by lia.
      specialize (IHa a'' b b' Ha2 Hb). pose proof (pairp_pos a'' b'). lia.
Qed.

Lemma lbd_pairp_mono_snd_lt : forall b b' a : nat,
  (b < b')%nat -> (pairp a b < pairp a b')%nat.
Proof.
  intros b b' a. revert b b'. induction a as [|a IHa]; intros b b' H; cbn [pairp].
  - lia.
  - specialize (IHa b b' H). lia.
Qed.

(* ===================================================================== *)
(* §C  HBL 三导出条件（层 1 主目标）                                              *)
(*     lbd_Box：有界可证性谓词——界 B 内存在凭证码 w 使 w 的自燃料重演恰为 ⌜目标⌝。     *)
(*     它就是 D2 的 Σ-原子（fsig）在平凡赋值下的取值，故是真正的语言内公式。           *)
(* ===================================================================== *)

Definition lbd_Box (B c : nat) : bool := bsearch B (fun w : nat => verPf w c).

(* MP 码级传递子：大前提凭证码 ci、小前提凭证码 cf 合成结论的凭证码 *)
Definition lbd_mpT (ci cf : nat) : nat := MPc ci cf.

(* 界闭包映射：界 B 内两张凭证码 MP 合成后的成本上界 *)
Definition lbd_boxup (B : nat) : nat := MPc B B.

(* 语言内身份钉死：lbd_Box 就是 Formula2 的 fsig Σ-原子取值（平凡赋值） *)
Lemma lbd_Box_lang_internal : forall B c : nat,
  lbd_Box B c = evalF2 (fsig (numT B) (numT c)) (fun _ : nat => 0).
Proof.
  intros B c. unfold lbd_Box. cbn [evalF2].
  rewrite valt_numT. rewrite valt_numT. reflexivity.
Qed.

(* Σ 反射半边的构造性补全：bool 证书升格为重演账——
   verPf w c = true 给出显式公式 g：dP2 w w = Some g 且 ⌜g⌝ = c *)
Theorem lbd_replay_upgrade : forall (w c : nat),
  verPf w c = true ->
  sigT (fun g : Formula =>
    (loeb_tid (option Formula) (dP2 w w) (Some g) *
     loeb_tid nat (gnF g) c)%type).
Proof.
  intros w c Hv. unfold verPf in Hv.
  destruct (dP2 w w) as [gg|] eqn:Ed.
  - cbv iota in Hv.
    apply (proj1 (Nat.eqb_eq (gnF gg) c)) in Hv.
    exists gg. split.
    + apply loeb_tid_refl.
    + apply loeb_tid_eq. exact Hv.
  - cbv iota in Hv. discriminate Hv.
Qed.

(* 升格后的一致燃料重演（燃料参数化定理形，与 gnPrf_replay 接口同型） *)
Theorem lbd_replay_uniform : forall (w c : nat) (g : Formula) (k : nat),
  verPf w c = true -> loeb_tid nat (gnF g) c -> (w <= k)%nat ->
  loeb_tid (option Formula) (dP2 k w) (Some g).
Proof.
  intros w c g k Hv Hc Hk.
  destruct (lbd_replay_upgrade w c Hv) as [gg [Ed Hcg]].
  tidQ Hcg Ecg. tidQ Hc Ech.
  (* ⌜gg⌝ = c = ⌜g⌝ ⟹ gg = g（编码单射），一致燃料重演即达 g *)
  assert (Hgg : gg = g).
  { apply (gnF_inj gg g). rewrite Ecg. symmetry. exact Ech. }
  apply loeb_tid_eq. rewrite (lbd_dP2_norm w k Hk). rewrite <- Hgg.
  tidQ Ed Ee. exact Ee.
Qed.

(* ── HBL1：必然化 ──
   ⊢ f（有 Prf 凭证）则 □_B⌜f⌝ 为真，界只需盖过凭证码。 *)
Theorem lbd_HBL1 : forall (f : Formula) (pf : Prf f) (B : nat),
  (S (gnPrf f pf) <= B)%nat -> lbd_Box B (gnF f) = true.
Proof.
  intros f pf B HB. unfold lbd_Box.
  tidQ (bsearch_witness B (fun w : nat => verPf w (gnF f)) (gnPrf f pf)
          (loeb_tid_eq bool (gnPrf f pf <? B) true
             ((proj2 (Nat.ltb_lt (gnPrf f pf) B)) HB))
          (verPf_ledger_sound (gnPrf f pf) f pf (loeb_tid_refl nat (gnPrf f pf)))) E.
  exact E.
Qed.

(* ── HBL3：K 形 ──
   □_B⌜f→g⌝ → □_B⌜f⌝ → □_{boxup B}⌜g⌝：两张低于界的凭证码经 lbd_mpT 合成，
   合成码低于界闭包 boxup B。 *)
Theorem lbd_HBL3 : forall (a b : Formula) (B : nat),
  lbd_Box B (gnF (fimp a b)) = true ->
  lbd_Box B (gnF a) = true ->
  lbd_Box (lbd_boxup B) (gnF b) = true.
Proof.
  intros a b B Heq1 Heq2. unfold lbd_Box in *.
  destruct (bsearch_character B (fun w : nat => verPf w (gnF (fimp a b)))
              (loeb_tid_eq _ _ _ Heq1)) as [w1 [Hlt1 Hv1]].
  destruct (bsearch_character B (fun w : nat => verPf w (gnF a))
              (loeb_tid_eq _ _ _ Heq2)) as [w2 [Hlt2 Hv2]].
  tidQ Hlt1 E1. pose proof (proj1 (Nat.ltb_lt w1 B) E1) as L1.
  tidQ Hlt2 E2. pose proof (proj1 (Nat.ltb_lt w2 B) E2) as L2.
  tidQ Hv1 Ev1. cbv beta in Ev1.
  tidQ Hv2 Ev2. cbv beta in Ev2.
  (* 升格为 ∀k 一致重演形（MPc_code_closed 的供账前提形） *)
  assert (Hmp1 : forall k : nat, (w1 <= k)%nat ->
                  loeb_tid (option Formula) (dP2 k w1) (Some (fimp a b))).
  { intros k Hk.
    exact (lbd_replay_uniform w1 (gnF (fimp a b)) (fimp a b) k
             Ev1 (loeb_tid_refl nat (gnF (fimp a b))) Hk). }
  assert (Hmp2 : forall k : nat, (w2 <= k)%nat ->
                  loeb_tid (option Formula) (dP2 k w2) (Some a)).
  { intros k Hk.
    exact (lbd_replay_uniform w2 (gnF a) a k
             Ev2 (loeb_tid_refl nat (gnF a)) Hk). }
  unfold lbd_mpT.
  pose proof (MPc_code_closed w1 w2 a b Hmp1 Hmp2 (MPc w1 w2)
                (Nat.le_refl (MPc w1 w2))) as Hmp.
  (* 界迁移：MPc w1 w2 < boxup B = pairp 7 (pairp B B)
     （w1 w2 皆严格低于 B：第二分量严格抬升 + 非严格单调链） *)
  assert (Hbnd : (MPc w1 w2 < lbd_boxup B)%nat).
  { unfold lbd_boxup, MPc.
    assert (Hm1 : (pairp w1 w2 < pairp w1 B)%nat)
      by (apply (lbd_pairp_mono_snd_lt w2 B w1); lia).
    assert (Hm2 : (pairp w1 B <= pairp B B)%nat)
      by (apply (lbd_pairp_mono w1 B B B); lia).
    assert (Hinner : (pairp w1 w2 < pairp B B)%nat).
    { apply Nat.lt_le_trans with (pairp w1 B).
      - exact Hm1.
      - exact Hm2. }
    apply (lbd_pairp_mono_snd_lt (pairp w1 w2) (pairp B B) 7).
    exact Hinner. }
  assert (Hver : verPf (MPc w1 w2) (gnF b) = true).
  { unfold verPf. tidQ Hmp Emp. rewrite Emp. cbv iota. apply Nat.eqb_refl. }
  tidQ (bsearch_witness (lbd_boxup B) (fun w : nat => verPf w (gnF b)) (MPc w1 w2)
          (loeb_tid_eq bool (MPc w1 w2 <? lbd_boxup B) true
             ((proj2 (Nat.ltb_lt (MPc w1 w2) (lbd_boxup B))) Hbnd))
          (loeb_tid_eq bool (verPf (MPc w1 w2) (gnF b)) true Hver)) Ebs.
  exact Ebs.
Qed.

(* ── HBL2：规则形 ──
   ⊢ f→g（有 Prf 凭证，码 cB）则 □_B⌜f⌝ → □_{boxup(pairp (S cB) B)}⌜g⌝：
   凭证码经 gnPrf_replay 一致重演供账，界闭包把两张码一并盖住。 *)
Theorem lbd_HBL2 : forall (a b : Formula) (pf : Prf (fimp a b)) (B cB : nat),
  (gnPrf (fimp a b) pf <= cB)%nat ->
  lbd_Box B (gnF a) = true ->
  lbd_Box (lbd_boxup (pairp (Datatypes.S cB) B)) (gnF b) = true.
Proof.
  intros a b pf B cB HcB Heq. unfold lbd_Box in *.
  destruct (bsearch_character B (fun w : nat => verPf w (gnF a))
              (loeb_tid_eq _ _ _ Heq)) as [w2 [Hlt2 Hv2]].
  tidQ Hlt2 E2. pose proof (proj1 (Nat.ltb_lt w2 B) E2) as L2.
  tidQ Hv2 Ev2. cbv beta in Ev2.
  (* 小前提证书升格为 ∀k 一致重演形 *)
  assert (Hmp2 : forall k : nat, (w2 <= k)%nat ->
                  loeb_tid (option Formula) (dP2 k w2) (Some a)).
  { intros k Hk.
    exact (lbd_replay_uniform w2 (gnF a) a k
             Ev2 (loeb_tid_refl nat (gnF a)) Hk). }
  unfold lbd_mpT.
  (* 大前提凭证码经 gnPrf_replay 一致重演供账（D1' 的直接使用） *)
  assert (Hb1 : forall k : nat, (gnPrf (fimp a b) pf <= k)%nat ->
                 loeb_tid (option Formula) (dP2 k (gnPrf (fimp a b) pf)) (Some (fimp a b)))
    by exact (gnPrf_replay (fimp a b) pf).
  pose proof (MPc_code_closed (gnPrf (fimp a b) pf) w2 a b Hb1 Hmp2
                (MPc (gnPrf (fimp a b) pf) w2)
                (Nat.le_refl (MPc (gnPrf (fimp a b) pf) w2))) as Hmp.
  (* 界迁移：pairp (S cB) B 盖过凭证码与界；boxup M = pairp 7 (pairp M M) *)
  assert (HM1 : (gnPrf (fimp a b) pf <= pairp (Datatypes.S cB) B)%nat).
  { pose proof (pairp_ge1 (Datatypes.S cB) B) as Hp. lia. }
  assert (HBM : (B <= pairp (Datatypes.S cB) B)%nat)
    by exact (pairp_ge (Datatypes.S cB) B).
  assert (HM2 : (w2 <= pairp (Datatypes.S cB) B)%nat) by lia.
  assert (Hbnd : (MPc (gnPrf (fimp a b) pf) w2
                   < lbd_boxup (pairp (Datatypes.S cB) B))%nat).
  { unfold lbd_boxup, MPc.
    assert (HM3 : (w2 < pairp (Datatypes.S cB) B)%nat) by lia.
    assert (Hm1 : (pairp (gnPrf (fimp a b) pf) w2
                    < pairp (gnPrf (fimp a b) pf) (pairp (Datatypes.S cB) B))%nat)
      by (apply (lbd_pairp_mono_snd_lt w2 (pairp (Datatypes.S cB) B)
                  (gnPrf (fimp a b) pf)); lia).
    assert (Hm2 : (pairp (gnPrf (fimp a b) pf) (pairp (Datatypes.S cB) B)
                    <= pairp (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B))%nat)
      by (apply (lbd_pairp_mono (gnPrf (fimp a b) pf) (pairp (Datatypes.S cB) B)
                  (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B)); lia).
    assert (Hinner : (pairp (gnPrf (fimp a b) pf) w2
                      < pairp (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B))%nat).
    { apply Nat.lt_le_trans with (pairp (gnPrf (fimp a b) pf)
                                        (pairp (Datatypes.S cB) B)).
      - exact Hm1.
      - exact Hm2. }
    apply (lbd_pairp_mono_snd_lt (pairp (gnPrf (fimp a b) pf) w2)
             (pairp (pairp (Datatypes.S cB) B) (pairp (Datatypes.S cB) B)) 7).
    exact Hinner. }
  assert (Hver : verPf (MPc (gnPrf (fimp a b) pf) w2) (gnF b) = true).
  { unfold verPf. tidQ Hmp Emp. rewrite Emp. cbv iota. apply Nat.eqb_refl. }
  tidQ (bsearch_witness (lbd_boxup (pairp (Datatypes.S cB) B))
          (fun w : nat => verPf w (gnF b)) (MPc (gnPrf (fimp a b) pf) w2)
          (loeb_tid_eq bool (MPc (gnPrf (fimp a b) pf) w2
                       <? lbd_boxup (pairp (Datatypes.S cB) B)) true
             ((proj2 (Nat.ltb_lt (MPc (gnPrf (fimp a b) pf) w2)
                       (lbd_boxup (pairp (Datatypes.S cB) B)))) Hbnd))
          (loeb_tid_eq bool (verPf (MPc (gnPrf (fimp a b) pf) w2) (gnF b)) true
             Hver)) Ebs.
  exact Ebs.
Qed.

(* ===================================================================== *)
(* §D  D3' 编码自涉展品（层 2）：对角句的 Löb 蕴含之盒有闭式可计算界                        *)
(*     使用 D1 对角引理（Defined，可提取）+ 本件 HBL1：任一元 th 的对角句                   *)
(*     d = diagF th 有 ⊢ th(⌜d⌝)→d（Prf 凭证），其凭证码 c* 直接给出盒真之界。             *)
(*     「守卫是构造性的」：界不是存在假设，而是 lbd_boxup c* 闭式计算。                    *)
(* ===================================================================== *)

Theorem lbd_diag_necessitation : forall th : Formula,
  unaryF th = true ->
  sigT (fun d : Formula =>
    sigT (fun pf : Prf (fimp (appN th (gnF d)) d) =>
      lbd_Box (lbd_boxup (gnPrf (fimp (appN th (gnF d)) d) pf))
              (gnF (fimp (appN th (gnF d)) d)) = true)).
Proof.
  intros th Hun.
  destruct (diagonal_lemma th (loeb_tid_eq bool (unaryF th) true Hun))
    as [d [Hcl [_ pfx]]].
  exists d. exists pfx.
  apply (lbd_HBL1 (fimp (appN th (gnF d)) d) pfx
           (lbd_boxup (gnPrf (fimp (appN th (gnF d)) d) pfx))).
  unfold lbd_boxup, MPc.
  pose proof (lbd_pairp_gt_snd (gnPrf (fimp (appN th (gnF d)) d) pfx)
               (gnPrf (fimp (appN th (gnF d)) d) pfx)) as H1.
  pose proof (pairp_ge 7 (pairp (gnPrf (fimp (appN th (gnF d)) d) pfx)
                          (gnPrf (fimp (appN th (gnF d)) d) pfx))) as H2.
  lia.
Qed.

(* ===================================================================== *)
(* 诚实边界（显式声明，不特设构造）：                                              *)
(*   1. 本件 HBL 三肢的对象理论即 G10 的 Prf（真闭方程+MP+repl），□ 以有界               *)
(*      bsearch 语义实现（lbd_Box = fsig 取值），□ 的真值由界与码账真实决定               *)
(*      （D2 Sigma_fires / Sigma_bound_tight 烟测的语义沿用）。                          *)
(*   2. 全形 Löb 不在本件（见头注 fail-loud：Formula2 编码往返 + 无界搜索墙），             *)
(*      降档形态为 guarded：lbd_diag_necessitation 给出守卫的闭式计算。                   *)
(*   3. dP2 解码唯一性方向（pairp 解码单射）仍未展开（D2 诚实边界 2 沿袭），              *)
(*      本件不依赖该方向。                                                        *)
(* ===================================================================== *)

(* —— 假设面自审（全部应 Closed under the global context） —— *)
Print Assumptions lbd_dP2_fuel_inv.
Print Assumptions lbd_replay_upgrade.
Print Assumptions lbd_HBL1.
Print Assumptions lbd_HBL3.
Print Assumptions lbd_HBL2.
Print Assumptions lbd_diag_necessitation.
