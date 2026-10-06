(* ============================================================ *)
(* abl_loeb_d3_prf2b.v — Formula2 凭证层第二段：dPrf2 解码器 + 码级重演              *)
(*   + MP2 码级封闭 + lbg_Box2（lbg_ 前缀；接 abl_loeb_d3_prf2，                    *)
(*   同池续建，CZ/DD/DS 前段已闭合语句零改动）                                       *)
(*                                                                *)
(*  使命: DS 前段「留给下一棒」清单四项的全数施工：                                   *)
(*   (1) dPrf2：Prf2 凭证码的全函数燃料解码器（照 D1 dP2 模式，燃料=递归护栏；          *)
(*         标签 12：prf2_lift——D1 证明码经 dP2 重演，升格 f2b；                       *)
(*         标签 13：prf2_mp——两张 Prf2 码重演 + lbe_gnF2 比对（可判定 MP 校验）；      *)
(*         标签 14：prf2_repl——th 经 lbe_dF2b、两代入项经 dT2，重演代入双条件；         *)
(*         标签 15：prf2_sig——四元组载荷 (⌜B⌝,⌜c⌝,⌜g⌝,⌜pf⌝) 全解，D1 证明码须经           *)
(*               dP2 重演成功（载荷整体证书化，伪码在 dP2 枝处拒绝）；                   *)
(*   (2) 码级重演：lbg_gnPrf2_replay（凭证码在任意充足燃料下重演恰回被证公式，           *)
(*         gnPrf_replay 的 Formula2 凭证层同构）+ 自燃料方程形；                        *)
(*   (3) MP2 封闭：MPc2（分离规则码层合成子 = pairp 13）纯码级封闭 + Prf2 供账形，        *)
(*         随即立 lbg_Box2（Prf2 层有界可证性盒谓词）：HBL1 必然化形 + HBL3 K 形            *)
(*         （界闭包 lbg_boxup2 = MPc2 B B，界迁移使用 CZ 单调性两件）；                 *)
(*   (4) 码空间分区补全（新解码器拒旧码两件）：dPrf2 拒绝一切 D1 证明码（标签 6–8）         *)
(*         与一切 Formula2 公式码（标签 9–11）——与 DS 前段两件（旧解码器拒新码）             *)
(*         合成五层码空间（0–3/4–5/6–8/9–11/12–15）在四个解码器值域上的双向互斥；         *)
(*   (5) 余量·假设消解（DD 接口建议 (b) 完备半边的闭项切片）：prf2_sig 的两条              *)
(*         元级前提（forall-s 值全称）对闭项 Σ-原子当场消解为纯 nat 证书——                *)
(*         lbg_prf2_sig_code：唯一前提是证明码的 nat 不等式 gnPrf g pf < m；             *)
(*         prf2_repl 的值等前提消解为代入项码相等（lbg_prf2_repl_code，经 gnT 单射）；    *)
(*         端到端展品：第一张码级证书化 Σ-原子凭证的编码→解码重演往返。                    *)
(*                                                                *)
(*  依赖: Require Import G10_LoebFam / abl_loeb_d3（lbd_dP2_fuel_inv、          *)
(*   lbd_unp2_self_bounds、lbd_pairp_mono 两件）/ abl_loeb_d3_ext（lbe_gnF2_fuel、          *)
(*   lbe_dF2b_fuel_inv、lbe_gnF2_inj）/ abl_loeb_d3_prf2（Prf2、gnPrf2、lbf_demo_*）。      *)
(*   编译配方: 先编供链 abl_loeb_d3.v → abl_loeb_d3_ext.v → abl_loeb_d3_prf2.v，再编本件：    *)
(*   rocq c -native-compiler no -q -Q <池> "" -Q <vo_local 树> "" <件>.v                  *)
(*   （Rocq 9.1.0，live switch；G10_LoebFam 从 vo_local_world_unified_0930 缓存               *)
(*   .vo 解析，池内不留其源码拷贝——坑卡 33 池影坑照防。）                                  *)
(*                                                                *)
(* 【本件陈述（四段 22 件）】                                                         *)
(*   §A dPrf2 解码器（标签 12–15）+ 燃料不变性 lbg_dPrf2_fuel_inv / lbg_dPrf2_norm          *)
(*       + 新解码器拒旧码两件；                                                          *)
(*   §B 码级重演：lbg_gnPrf2_replay（四枝主情形 + 四枝燃料耗尽）+ 自燃料方程形；             *)
(*   §C MP2 封闭：MPc2 / lbg_MPc2_code_closed / lbg_MPc2_prf_closed +                      *)
(*       lbg_verPf2 / lbg_Box2 / lbg_boxup2 + lbg_verPf2_ledger_sound +                    *)
(*       lbg_replay2_uniform + lbg_Box2_HBL1 / lbg_Box2_HBL3；                            *)
(*   §D 假设消解与展品：lbg_gnT_inj / lbg_prf2_repl_code / lbg_prf2_sig_code +             *)
(*       lbg_demo_row_code（闭项 Σ-原子的码级证书化凭证）+ 其 sound 实例与                  *)
(*       端到端重演实例。                                                              *)
(*                                                                *)
(*  构造性: Set 载体纪律，语句面零 Prop：dPrf2/lbg_verPf2/lbg_Box2 为 bool/nat        *)
(*   全函数；重演与封闭定理由 loeb_tid 载体承担（与 D1 gnPrf_replay、D2 MPc 封闭同型）；      *)
(*   §D 两定理把元级 forall-s 前提消解为纯 nat 前提（< 与 =），交付面零悬置假设；            *)
(*   零 Variable/Hypothesis、零公理、零承认、零占位、零经典逻辑；全链信息性，可提取。           *)
(*                                                                *)
(* 【诚实边界（fail-loud，同步登记于施工报告）】                                        *)
(*   1. dPrf2 只重演被证公式、不重构 Prf2 凭证（prf2_sig/prf2_repl 的元级前提是外延            *)
(*      tid 值等，原理上不可从码重构——D2 坑卡同型边界）；凭证以一等分量随行登记，              *)
(*      由 lbf_Prf2_sound 元级可靠性承担。                                              *)
(*   2. §D 的假设消解是闭项切片：B、c 须为 numT 形（闭项），非闭项的界/槽前提                  *)
(*      证书化（一般 dT2 证书与界前提弱化）仍是后续山峰；Σ-原子真 ⇒ 可证的完备半边              *)
(*      被无界搜索墙（rLPO 谱系）阻断——dP2 重演不重构凭证，故 lbg_verPf2 为真不含              *)
(*      Prf2 凭证存在性，本件不立也不伪造该方向。                                       *)
(*   3. lbg_Box2 是 Prf2 层自有盒谓词（验证器为 dPrf2 驱动），与 D1 层 lbd_Box             *)
(*      （验证器为 dP2 驱动）不同值域：lbd_Box 的语言内身份是 fsig 取值（CZ                 *)
(*      lbd_Box_lang_internal），lbg_Box2 无对应语言内身份定理，本件不伪造。                *)
(*   禁拼凑：解码器、重演、封闭、盒谓词全部真 Fixpoint/真归纳组装，无占位收尾。               *)
(* ============================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Require Import G10_LoebFam.
Require Import abl_loeb_d3.
Require Import abl_loeb_d3_ext.
Require Import abl_loeb_d3_prf2.

(* ===================================================================== *)
(* §A  dPrf2：Prf2 凭证码的全函数燃料解码器（标签 12–15）                                    *)
(* ===================================================================== *)

(* 照 dP2 模式（燃料 = 递归护栏，解码的是码而非燃料）：
     标签 12：prf2_lift —— D1 证明码经 dP2 重演恰回 g，升格 f2b g；
     标签 13：prf2_mp   —— 两张 Prf2 码重演（大前提须解为 fimp2，且小前提重演式的
            F2 码与 lbe_gnF2 比对一致：可判定 MP 校验），重演 MP 结论；
     标签 14：prf2_repl —— th 码经 lbe_dF2b、两代入项码经 dT2 解出，重演代入双条件；
     标签 15：prf2_sig  —— 四元组载荷 (⌜B⌝,⌜c⌝,⌜g⌝,⌜pf⌝)：B、c 经 dT2、目标公式经
            dF2、D1 证明码经 dP2 全部解出（证明码解不出则整码拒绝——载荷整体
            证书化），重演 Σ-原子。 *)
Fixpoint dPrf2 (f c : nat) {struct f} : option Formula2 :=
  match f with
  | O => None
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))))))), q) =>
          (match dP2 f' q with
           | Some g => Some (f2b g)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))))))))), q) =>
          (match unp2 q q with
           | Some (w1, w2) =>
               (match dPrf2 f' w1 with
                | Some (fimp2 u v) =>
                    (match dPrf2 f' w2 with
                     | Some z =>
                         if Nat.eqb (lbe_gnF2 z) (lbe_gnF2 u) then Some v else None
                     | None => None
                     end)
                | _ => None
                end)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))))))))), q) =>
          (match unp2 q q with
           | Some (p, r) =>
               (match unp2 p p with
                | Some (a, b) =>
                    (match lbe_dF2b f' a with
                     | Some th =>
                         (match dT2 f' b with
                          | Some x =>
                              (match dT2 f' r with
                               | Some y =>
                                   Some (fimp2 (substF2 th x) (substF2 th y))
                               | None => None
                               end)
                          | None => None
                          end)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))))))))))), q) =>
          (match unp2 q q with
           | Some (p, r) =>
               (match unp2 p p with
                | Some (a, b) =>
                    (match unp2 r r with
                     | Some (e, m) =>
                         (match dT2 f' a with
                          | Some x =>
                              (match dT2 f' b with
                               | Some y =>
                                   (match dF2 f' e with
                                    | Some h =>
                                        (match dP2 f' m with
                                         | Some _ => Some (fsig x y)
                                         | None => None
                                         end)
                                    | None => None
                                    end)
                               | None => None
                               end)
                          | None => None
                          end)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

(* 解码器燃料不变性：解码的是码而非燃料（lbd_dP2_fuel_inv 的 Prf2 码层同型推广；
   使用 lbd_unp2_self_bounds + lbd_dT2/dF2/dP2_fuel_inv + lbe_dF2b_fuel_inv；
   标签 13 枝沿 dPrf2 自身归纳）。 *)
Lemma lbg_dPrf2_fuel_inv : forall c k1 k2 : nat,
  (c <= k1)%nat -> (c <= k2)%nat -> dPrf2 k1 c = dPrf2 k2 c.
Proof.
  intros c. induction c as [c IH] using lt_wf_ind. intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; reflexivity.
  - destruct k1 as [|k1']; [lia|]. destruct k2 as [|k2']; [lia|].
    cbn [dPrf2].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota.
      destruct l as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|l3]]]]]]]]]]]]]]]]; cbv iota; try reflexivity.
      * (* 标签 12：prf2_lift，dP2 一路 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))))))))) q Epc) as Hb1.
        destruct Hb1 as [_ [Hq Hqslt]].
        assert (Ha1 : (q <= k1')%nat) by lia.
        assert (Ha2 : (q <= k2')%nat) by lia.
        rewrite (lbd_dP2_fuel_inv q k1' k2' Ha1 Ha2). reflexivity.
      * (* 标签 13：prf2_mp，两张子凭证码沿 dPrf2 自身不变性 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))))))))) q Epc) as Hb1.
        destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[w1 w2]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q w1 w2 Epq) as Hb2.
        destruct Hb2 as [Hw1 [Hw2 Hw2lt]].
        assert (Hl1 : (w1 < Datatypes.S c')%nat) by lia.
        assert (Hl2 : (w2 < Datatypes.S c')%nat) by lia.
        assert (Hu1 : (w1 <= k1')%nat) by lia.
        assert (Hu2 : (w1 <= k2')%nat) by lia.
        assert (Hv1 : (w2 <= k1')%nat) by lia.
        assert (Hv2 : (w2 <= k2')%nat) by lia.
        rewrite (IH w1 Hl1 k1' k2' Hu1 Hu2). rewrite (IH w2 Hl2 k1' k2' Hv1 Hv2).
        reflexivity.
      * (* 标签 14：prf2_repl，lbe_dF2b 一路 + dT2 两路 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))))))))))) q Epc) as Hb1.
        destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[p r]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q p r Epq) as Hb2.
        destruct Hb2 as [Hp [Hr Hrlt]].
        destruct (unp2 p p) as [[a b]|] eqn:Epp; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds p a b Epp) as Hb3.
        destruct Hb3 as [Hpa [Hpb _]].
        assert (Hfa1 : (a <= k1')%nat) by lia.
        assert (Hfa2 : (a <= k2')%nat) by lia.
        assert (Hfb1 : (b <= k1')%nat) by lia.
        assert (Hfb2 : (b <= k2')%nat) by lia.
        assert (Hfr1 : (r <= k1')%nat) by lia.
        assert (Hfr2 : (r <= k2')%nat) by lia.
        assert (Hf2 : lbe_dF2b k1' a = lbe_dF2b k2' a)
          by (apply lbe_dF2b_fuel_inv; lia).
        assert (Htb : dT2 k1' b = dT2 k2' b) by (apply lbd_dT2_fuel_inv; lia).
        assert (Htr : dT2 k1' r = dT2 k2' r) by (apply lbd_dT2_fuel_inv; lia).
        rewrite Hf2, Htb, Htr. reflexivity.
      * (* 标签 15：prf2_sig，四元组载荷：dT2 两路 + dF2 一路 + dP2 一路 *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c')
                     (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))))))))))) q Epc) as Hb1.
        destruct Hb1 as [_ [Hq Hqslt]].
        destruct (unp2 q q) as [[p r]|] eqn:Epq; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds q p r Epq) as Hb2.
        destruct Hb2 as [Hp [Hr Hrlt]].
        destruct (unp2 p p) as [[a b]|] eqn:Epp; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds p a b Epp) as Hb3.
        destruct Hb3 as [Hpa [Hpb _]].
        destruct (unp2 r r) as [[e m]|] eqn:Erm; cbv iota; try reflexivity.
        pose proof (lbd_unp2_self_bounds r e m Erm) as Hb4.
        destruct Hb4 as [He [Hm _]].
        assert (Hta1 : (a <= k1')%nat) by lia.
        assert (Hta2 : (a <= k2')%nat) by lia.
        assert (Htb1 : (b <= k1')%nat) by lia.
        assert (Htb2 : (b <= k2')%nat) by lia.
        assert (Hte1 : (e <= k1')%nat) by lia.
        assert (Hte2 : (e <= k2')%nat) by lia.
        assert (Htm1 : (m <= k1')%nat) by lia.
        assert (Htm2 : (m <= k2')%nat) by lia.
        assert (Hta : dT2 k1' a = dT2 k2' a) by (apply lbd_dT2_fuel_inv; lia).
        assert (Htb : dT2 k1' b = dT2 k2' b) by (apply lbd_dT2_fuel_inv; lia).
        assert (Hfe : dF2 k1' e = dF2 k2' e) by (apply lbd_dF2_fuel_inv; lia).
        assert (Hfm : dP2 k1' m = dP2 k2' m) by (apply lbd_dP2_fuel_inv; lia).
        rewrite Hta, Htb, Hfe, Hfm. reflexivity.
    + reflexivity.
Qed.

(* 自燃料规范化推论（lbd_dP2_norm 同型） *)
Corollary lbg_dPrf2_norm : forall c k : nat, (c <= k)%nat -> dPrf2 k c = dPrf2 c c.
Proof.
  intros c k H. apply (lbg_dPrf2_fuel_inv c k c); [exact H | apply Nat.le_refl].
Qed.

(* ── 码空间分区补全（新解码器拒旧码两件）──
   dPrf2 只认标签 12–15：D1 证明码（标签 6–8）与 Formula2 公式码（标签 9–11）
   一律拒绝。与 DS 前段两件（dP2/lbe_dF2b 拒绝 Prf2 码）合成四个解码器值域上
   五层码空间（0–3/4–5/6–8/9–11/12–15）的双向互斥。 *)

Lemma lbg_dPrf2_gnPrf_none : forall (f : Formula) (pf : Prf f) (k : nat),
  dPrf2 k (gnPrf f pf) = None.
Proof.
  intros f pf k. destruct k as [|k'].
  - reflexivity.
  - destruct pf as [u1 u2 Hv | a b pf1 pf2 | th t1 t2 Hv];
      cbn [gnPrf dPrf2]; rewrite unp2_pair; cbv iota; reflexivity.
Qed.

Lemma lbg_dPrf2_lbe_gnF2_none : forall (f2 : Formula2) (k : nat),
  dPrf2 k (lbe_gnF2 f2) = None.
Proof.
  intros f2 k. destruct k as [|k'].
  - reflexivity.
  - destruct f2 as [g | B c | a b];
      cbn [lbe_gnF2 dPrf2]; rewrite unp2_pair; cbv iota; reflexivity.
Qed.

(* ===================================================================== *)
(* §B  码级重演：凭证码在任意充足燃料下重演恰回被证公式                                        *)
(* ===================================================================== *)

(* 凭证码恒正（燃料耗尽枝的矛盾供给） *)
Lemma lbg_gnPrf2_pos : forall (f2 : Formula2) (pf : Prf2 f2),
  (1 <= gnPrf2 f2 pf)%nat.
Proof.
  intros f2 pf.
  destruct pf as [g pf0 | a b pf1 pf2 | th t1 t2 Hv | B c g pf0 Hb Hc];
    cbn [gnPrf2]; apply pairp_pos.
Qed.

(* 带标签配对的严格界：标签非零时第二分量被严格超越（重演主情形把
   「子码 ≤ 码 ≤ S k′」升为「子码 ≤ k′」的承重件） *)
Lemma lbg_pairp_tag_lt : forall t z : nat, (z < pairp (Datatypes.S t) z)%nat.
Proof.
  intros t z. cbn [pairp].
  pose proof (pairp_ge t z) as H1. pose proof (pairp_pos t z) as H2. lia.
Qed.

(* ═══ 本段主定理（码级重演）：Prf2 凭证的码经 dPrf2 在任意充足燃料下重演，
       恰好得到被证公式 —— gnPrf_replay 的 Formula2 凭证层同构。
       四枝：lift 走 gnPrf_replay（账本连续性在重演层的兑现）；
       mp 走两张子凭证码重演 + lbe_gnF2 比对反射（Nat.eqb_refl 满足）；
       repl 走 lbe_gnF2_fuel + gnT_fuel×2；
       sig 走 gnT_fuel×2 + gnF_fuel + gnPrf_replay（四元组载荷全解）。 ═══ *)
Theorem lbg_gnPrf2_replay : forall (f2 : Formula2) (pf : Prf2 f2) (k : nat),
  (gnPrf2 f2 pf <= k)%nat ->
  loeb_tid (option Formula2) (dPrf2 k (gnPrf2 f2 pf)) (Some f2).
Proof.
  intros f2 pf.
  induction pf as
    [g pf0 | a b pf1 IH1 pf2 IH2 | th t1 t2 Hv | B c g pf0 Hb Hc]; intros k Hk;
    destruct k as [|k'].
  - (* prf2_lift，燃料耗尽：凭证码恒正，矛盾 *)
    pose proof (lbg_gnPrf2_pos _ (prf2_lift g pf0)) as Hp. lia.
  - (* prf2_lift 主情形：D1 证明码经 gnPrf_replay 重演，升格 f2b *)
    cbn [gnPrf2] in Hk.
    pose proof (lbg_pairp_tag_lt 11 (gnPrf g pf0)) as Hq1.
    assert (Hb1 : (gnPrf g pf0 <= k')%nat) by lia.
    cbn [gnPrf2 dPrf2].
    rewrite unp2_pair. cbv iota.
    tidQ (gnPrf_replay g pf0 k' Hb1) E. rewrite E. cbv iota.
    apply loeb_tid_refl.
  - (* prf2_mp，燃料耗尽 *)
    pose proof (lbg_gnPrf2_pos _ (prf2_mp a b pf1 pf2)) as Hp. lia.
  - (* prf2_mp 主情形：两张子凭证码重演 + lbe_gnF2 比对反射 *)
    cbn [gnPrf2] in Hk.
    pose proof (lbg_pairp_tag_lt 12
                  (pairp (gnPrf2 (fimp2 a b) pf1) (gnPrf2 a pf2))) as Hq1.
    pose proof (pairp_ge1 (gnPrf2 (fimp2 a b) pf1) (gnPrf2 a pf2)) as Hq2.
    pose proof (pairp_ge (gnPrf2 (fimp2 a b) pf1) (gnPrf2 a pf2)) as Hq3.
    assert (Hb1 : (gnPrf2 (fimp2 a b) pf1 <= k')%nat) by lia.
    assert (Hb2 : (gnPrf2 a pf2 <= k')%nat) by lia.
    cbn [gnPrf2 dPrf2].
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    tidQ (IH1 k' Hb1) E1. rewrite E1. cbv iota.
    tidQ (IH2 k' Hb2) E2. rewrite E2. cbv iota.
    rewrite Nat.eqb_refl.
    apply loeb_tid_refl.
  - (* prf2_repl，燃料耗尽 *)
    pose proof (lbg_gnPrf2_pos _ (prf2_repl th t1 t2 Hv)) as Hp. lia.
  - (* prf2_repl 主情形：th 经 lbe_gnF2_fuel、两代入项经 gnT_fuel *)
    cbn [gnPrf2] in Hk.
    pose proof (lbg_pairp_tag_lt 13
                  (pairp (pairp (lbe_gnF2 th) (gnT t1)) (gnT t2))) as Hq1.
    pose proof (pairp_ge1 (pairp (lbe_gnF2 th) (gnT t1)) (gnT t2)) as Hq2.
    pose proof (pairp_ge (pairp (lbe_gnF2 th) (gnT t1)) (gnT t2)) as Hq3.
    pose proof (pairp_ge1 (lbe_gnF2 th) (gnT t1)) as Hq4.
    pose proof (pairp_ge (lbe_gnF2 th) (gnT t1)) as Hq5.
    assert (Hb1 : (lbe_gnF2 th <= k')%nat) by lia.
    assert (Hb2 : (gnT t1 <= k')%nat) by lia.
    assert (Hb3 : (gnT t2 <= k')%nat) by lia.
    cbn [gnPrf2 dPrf2].
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite (lbe_gnF2_fuel th k' Hb1). cbv iota.
    rewrite (gnT_fuel t1 k' Hb2). cbv iota.
    rewrite (gnT_fuel t2 k' Hb3). cbv iota.
    apply loeb_tid_refl.
  - (* prf2_sig，燃料耗尽 *)
    pose proof (lbg_gnPrf2_pos _ (prf2_sig B c g pf0 Hb Hc)) as Hp. lia.
  - (* prf2_sig 主情形：四元组载荷全解（D1 证明码经 gnPrf_replay） *)
    cbn [gnPrf2] in Hk.
    pose proof (lbg_pairp_tag_lt 14
                  (pairp (pairp (gnT B) (gnT c)) (pairp (gnF g) (gnPrf g pf0)))) as Hq1.
    pose proof (pairp_ge1 (pairp (gnT B) (gnT c))
                  (pairp (gnF g) (gnPrf g pf0))) as Hq2.
    pose proof (pairp_ge (pairp (gnT B) (gnT c))
                  (pairp (gnF g) (gnPrf g pf0))) as Hq3.
    pose proof (pairp_ge1 (gnT B) (gnT c)) as Hq4.
    pose proof (pairp_ge (gnT B) (gnT c)) as Hq5.
    pose proof (pairp_ge1 (gnF g) (gnPrf g pf0)) as Hq6.
    pose proof (pairp_ge (gnF g) (gnPrf g pf0)) as Hq7.
    assert (Hb1 : (gnT B <= k')%nat) by lia.
    assert (Hb2 : (gnT c <= k')%nat) by lia.
    assert (Hb3 : (gnF g <= k')%nat) by lia.
    assert (Hb4 : (gnPrf g pf0 <= k')%nat) by lia.
    cbn [gnPrf2 dPrf2].
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite (gnT_fuel B k' Hb1). cbv iota.
    rewrite (gnT_fuel c k' Hb2). cbv iota.
    rewrite (gnF_fuel g k' Hb3). cbv iota.
    tidQ (gnPrf_replay g pf0 k' Hb4) E4. rewrite E4. cbv iota.
    apply loeb_tid_refl.
Qed.

(* 自燃料重演的方程形式（Proof 内部重写用） *)
Corollary lbg_gnPrf2_replay_eq : forall (f2 : Formula2) (pf : Prf2 f2),
  dPrf2 (gnPrf2 f2 pf) (gnPrf2 f2 pf) = Some f2.
Proof.
  intros f2 pf.
  tidQ (lbg_gnPrf2_replay f2 pf (gnPrf2 f2 pf) (Nat.le_refl (gnPrf2 f2 pf))) E.
  exact E.
Qed.

(* ===================================================================== *)
(* §C  MP2 码级封闭【D3 凭证层】+ lbg_Box2（Prf2 层有界可证性盒谓词）                          *)
(* ===================================================================== *)

(* MP 码级合成子的 Prf2 层对应：大前提凭证码 c1、小前提凭证码 c2 合成结论凭证码 *)
Definition MPc2 (c1 c2 : nat) : nat := pairp 13 (pairp c1 c2).

(* 纯码级封闭：两张凭证码（及各自充足燃料）合成的新码，在任意充足燃料下
   重演恰为 MP 结论——dPrf2 标签 13 枝的 lbe_gnF2 比对被 Nat.eqb_refl 反射满足。 *)
Theorem lbg_MPc2_code_closed : forall (c1 c2 : nat) (a b : Formula2),
  (forall k : nat, (c1 <= k)%nat ->
     loeb_tid (option Formula2) (dPrf2 k c1) (Some (fimp2 a b))) ->
  (forall k : nat, (c2 <= k)%nat ->
     loeb_tid (option Formula2) (dPrf2 k c2) (Some a)) ->
  forall k : nat, (MPc2 c1 c2 <= k)%nat ->
  loeb_tid (option Formula2) (dPrf2 k (MPc2 c1 c2)) (Some b).
Proof.
  intros c1 c2 a b H1 H2 k Hk. unfold MPc2 in Hk |- *.
  destruct k as [|k'].
  - pose proof (pairp_pos 13 (pairp c1 c2)) as Hp. lia.
  - cbn [dPrf2].
    pose proof (lbg_pairp_tag_lt 12 (pairp c1 c2)) as Hq1.
    pose proof (pairp_ge1 c1 c2) as Hq2.
    pose proof (pairp_ge c1 c2) as Hq3.
    assert (Hb1 : (c1 <= k')%nat) by lia.
    assert (Hb2 : (c2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    tidQ (H1 k' Hb1) E1. rewrite E1. cbv iota.
    tidQ (H2 k' Hb2) E2. rewrite E2. cbv iota.
    rewrite Nat.eqb_refl.
    apply loeb_tid_refl.
Qed.

(* Prf2 供账形：MP 凭证经重演直接供账（MPc_prf_closed 同型） *)
Theorem lbg_MPc2_prf_closed : forall (a b : Formula2)
  (pf1 : Prf2 (fimp2 a b)) (pf2 : Prf2 a) (k : nat),
  (gnPrf2 b (prf2_mp a b pf1 pf2) <= k)%nat ->
  loeb_tid (option Formula2)
    (dPrf2 k (MPc2 (gnPrf2 (fimp2 a b) pf1) (gnPrf2 a pf2))) (Some b).
Proof.
  intros a b pf1 pf2 k Hk.
  apply (lbg_MPc2_code_closed (gnPrf2 (fimp2 a b) pf1) (gnPrf2 a pf2) a b
    (lbg_gnPrf2_replay (fimp2 a b) pf1) (lbg_gnPrf2_replay a pf2) k).
  cbn [gnPrf2] in Hk. unfold MPc2. exact Hk.
Qed.

(* Prf2 层验证器与有界可证性盒谓词（lbd_Box 的凭证层对应；验证器为 dPrf2 驱动，
   与 D1 层 verPf/lbd_Box 值域互斥——分区两件） *)
Definition lbg_verPf2 (w c : nat) : bool :=
  match dPrf2 w w with
  | Some g => Nat.eqb (lbe_gnF2 g) c
  | None => false
  end.

Definition lbg_Box2 (B c : nat) : bool := bsearch B (fun w : nat => lbg_verPf2 w c).

(* 界闭包映射：MP2 合成的成本上界（lbd_boxup2 的 Prf2 层对应） *)
Definition lbg_boxup2 (B : nat) : nat := MPc2 B B.

(* Σ 反射半边的凭证层形态：与凭证码对齐的 w 必过 lbg_verPf2 验证 *)
Theorem lbg_verPf2_ledger_sound : forall (w : nat) (f2 : Formula2) (pf : Prf2 f2),
  loeb_tid nat w (gnPrf2 f2 pf) ->
  loeb_tid bool (lbg_verPf2 w (lbe_gnF2 f2)) true.
Proof.
  intros w f2 pf Hw. apply loeb_tid_eq. unfold lbg_verPf2.
  tidQ Hw E. rewrite E.
  rewrite (lbg_gnPrf2_replay_eq f2 pf). cbv iota. apply Nat.eqb_refl.
Qed.

(* 验证证书的一致燃料重演升格（lbd_replay_uniform 同型，使用 lbg_dPrf2_norm
   + lbe_gnF2_inj） *)
Theorem lbg_replay2_uniform : forall (w c : nat) (f2 : Formula2) (k : nat),
  lbg_verPf2 w c = true -> loeb_tid nat (lbe_gnF2 f2) c -> (w <= k)%nat ->
  loeb_tid (option Formula2) (dPrf2 k w) (Some f2).
Proof.
  intros w c f2 k Hv Hc Hk.
  unfold lbg_verPf2 in Hv.
  destruct (dPrf2 w w) as [gg|] eqn:Ed.
  - cbv iota in Hv.
    pose proof (proj1 (Nat.eqb_eq (lbe_gnF2 gg) c) Hv) as Egc.
    tidQ Hc Ech.
    assert (Hgg : gg = f2).
    { apply (lbe_gnF2_inj gg f2). rewrite Egc. symmetry. exact Ech. }
    apply loeb_tid_eq. rewrite (lbg_dPrf2_norm w k Hk). rewrite <- Hgg.
    exact Ed.
  - cbv iota in Hv. discriminate Hv.
Qed.

(* ── Box2 HBL1：必然化 ──
   ⊢₂ f2（有 Prf2 凭证）则 □₂_B⌜f2⌝ 为真，界只需盖过凭证码。 *)
Theorem lbg_Box2_HBL1 : forall (f2 : Formula2) (pf : Prf2 f2) (B : nat),
  (S (gnPrf2 f2 pf) <= B)%nat -> lbg_Box2 B (lbe_gnF2 f2) = true.
Proof.
  intros f2 pf B HB. unfold lbg_Box2.
  tidQ (bsearch_witness B (fun w : nat => lbg_verPf2 w (lbe_gnF2 f2))
          (gnPrf2 f2 pf)
          (loeb_tid_eq bool (gnPrf2 f2 pf <? B) true
             ((proj2 (Nat.ltb_lt (gnPrf2 f2 pf) B)) HB))
          (lbg_verPf2_ledger_sound (gnPrf2 f2 pf) f2 pf
             (loeb_tid_refl nat (gnPrf2 f2 pf)))) E.
  exact E.
Qed.

(* ── Box2 HBL3：K 形 ──
   □₂_B⌜fimp2 a b⌝ → □₂_B⌜a⌝ → □₂_{boxup2 B}⌜b⌝：两张低于界的凭证码经 MPc2 合成，
   合成码低于界闭包 boxup2 B——HBL 的 K 导出规则在 Prf2 凭证层自身重立
   （lbd_HBL3 的凭证层同构；界迁移使用 CZ 单调性两件）。 *)
Theorem lbg_Box2_HBL3 : forall (a b : Formula2) (B : nat),
  lbg_Box2 B (lbe_gnF2 (fimp2 a b)) = true ->
  lbg_Box2 B (lbe_gnF2 a) = true ->
  lbg_Box2 (lbg_boxup2 B) (lbe_gnF2 b) = true.
Proof.
  intros a b B Heq1 Heq2. unfold lbg_Box2 in *.
  destruct (bsearch_character B (fun w : nat => lbg_verPf2 w (lbe_gnF2 (fimp2 a b)))
              (loeb_tid_eq _ _ _ Heq1)) as [w1 [Hlt1 Hv1]].
  destruct (bsearch_character B (fun w : nat => lbg_verPf2 w (lbe_gnF2 a))
              (loeb_tid_eq _ _ _ Heq2)) as [w2 [Hlt2 Hv2]].
  tidQ Hlt1 E1. pose proof (proj1 (Nat.ltb_lt w1 B) E1) as L1.
  tidQ Hlt2 E2. pose proof (proj1 (Nat.ltb_lt w2 B) E2) as L2.
  tidQ Hv1 Ev1. cbv beta in Ev1.
  tidQ Hv2 Ev2. cbv beta in Ev2.
  (* 两张验证证书升格为 ∀k 一致重演形（lbg_MPc2_code_closed 的供账前提形） *)
  assert (Hmp1 : forall k : nat, (w1 <= k)%nat ->
                  loeb_tid (option Formula2) (dPrf2 k w1) (Some (fimp2 a b))).
  { intros k Hk.
    exact (lbg_replay2_uniform w1 (lbe_gnF2 (fimp2 a b)) (fimp2 a b) k
             Ev1 (loeb_tid_refl nat (lbe_gnF2 (fimp2 a b))) Hk). }
  assert (Hmp2 : forall k : nat, (w2 <= k)%nat ->
                  loeb_tid (option Formula2) (dPrf2 k w2) (Some a)).
  { intros k Hk.
    exact (lbg_replay2_uniform w2 (lbe_gnF2 a) a k
             Ev2 (loeb_tid_refl nat (lbe_gnF2 a)) Hk). }
  pose proof (lbg_MPc2_code_closed w1 w2 a b Hmp1 Hmp2 (MPc2 w1 w2)
                (Nat.le_refl (MPc2 w1 w2))) as Hmp.
  (* 界迁移：MPc2 w1 w2 < boxup2 B = pairp 13 (pairp B B) *)
  assert (Hbnd : (MPc2 w1 w2 < lbg_boxup2 B)%nat).
  { unfold MPc2, lbg_boxup2.
    assert (Hm1 : (pairp w1 w2 < pairp w1 B)%nat)
      by (apply (lbd_pairp_mono_snd_lt w2 B w1); lia).
    assert (Hm2 : (pairp w1 B <= pairp B B)%nat)
      by (apply (lbd_pairp_mono w1 B B B); lia).
    assert (Hinner : (pairp w1 w2 < pairp B B)%nat).
    { apply Nat.lt_le_trans with (pairp w1 B).
      - exact Hm1.
      - exact Hm2. }
    apply (lbd_pairp_mono_snd_lt (pairp w1 w2) (pairp B B) 13).
    exact Hinner. }
  assert (Hver : lbg_verPf2 (MPc2 w1 w2) (lbe_gnF2 b) = true).
  { unfold lbg_verPf2. tidQ Hmp Emp. rewrite Emp. cbv iota. apply Nat.eqb_refl. }
  tidQ (bsearch_witness (lbg_boxup2 B)
          (fun w : nat => lbg_verPf2 w (lbe_gnF2 b)) (MPc2 w1 w2)
          (loeb_tid_eq bool (MPc2 w1 w2 <? lbg_boxup2 B) true
             ((proj2 (Nat.ltb_lt (MPc2 w1 w2) (lbg_boxup2 B))) Hbnd))
          (loeb_tid_eq bool (lbg_verPf2 (MPc2 w1 w2) (lbe_gnF2 b)) true Hver)) Ebs.
  exact Ebs.
Qed.

(* ===================================================================== *)
(* §D  余量·假设消解：prf2_sig / prf2_repl 前提的码级证书化                                     *)
(*     （DD 接口建议 (b) 完备半边的闭项切片）                                              *)
(* ===================================================================== *)

(* gnT 单射（gnT_fuel 的直接推论，repl 码级证书的承重件） *)
Lemma lbg_gnT_inj : forall t1 t2 : Term, gnT t1 = gnT t2 -> t1 = t2.
Proof.
  intros t1 t2 H.
  pose proof (gnT_fuel t1 (gnT t1) (Nat.le_refl (gnT t1))) as E1.
  pose proof (gnT_fuel t2 (gnT t2) (Nat.le_refl (gnT t2))) as E2.
  rewrite H in E1. rewrite E1 in E2. inversion E2. reflexivity.
Qed.

(* prf2_repl 的码级证书形：值全称前提（forall s, valt t1 s = valt t2 s 的 tid 形）
   当场消解为代入项的码级方程 gnT t1 = gnT t2——元级值等被码相等解消。 *)
Theorem lbg_prf2_repl_code : forall (th : Formula2) (t1 t2 : Term),
  (gnT t1 = gnT t2)%nat -> Prf2 (fimp2 (substF2 th t1) (substF2 th t2)).
Proof.
  intros th t1 t2 Hc. apply (prf2_repl th t1 t2).
  intros s. apply loeb_tid_eq.
  pose proof (lbg_gnT_inj t1 t2 Hc) as Ht. rewrite Ht. reflexivity.
Qed.

(* prf2_sig 的码级证书形（闭项 Σ-原子）：两条元级 forall-s 前提当场消解为
   一条纯 nat 不等式——界前提经 valt_numT 化为 gnPrf g pf < m；
   槽前提在 c := numT (gnF g) 下恒真（valt_numT 一步）。 *)
Theorem lbg_prf2_sig_code : forall (m : nat) (g : Formula) (pf : Prf g),
  (gnPrf g pf < m)%nat -> Prf2 (fsig (numT m) (numT (gnF g))).
Proof.
  intros m g pf Hlt. apply (prf2_sig (numT m) (numT (gnF g)) g pf).
  - intros s. apply loeb_tid_eq. rewrite valt_numT.
    apply (proj2 (Nat.ltb_lt (gnPrf g pf) m)). exact Hlt.
  - intros s. apply loeb_tid_eq. rewrite valt_numT. reflexivity.
Qed.

(* 展品：DS 前段第一张账本行（证明码 2624 < 3000）的码级证书化重建 *)
Lemma lbg_demo_row_lt : (gnPrf (teq tzero tzero) lbf_demo_pf0 < 3000)%nat.
Proof. vm_compute. lia. Qed.

Definition lbg_demo_row_code : Prf2 lbf_demo_atom :=
  lbg_prf2_sig_code 3000 (teq tzero tzero) lbf_demo_pf0 lbg_demo_row_lt.

(* 展品一：码级证书化凭证的元级可靠性（lbf_Prf2_sound 实例） *)
Theorem lbg_demo_row_code_sound :
  loeb_tid bool (evalF2 lbf_demo_atom (fun _ : nat => 0)) true.
Proof. exact (lbf_Prf2_sound lbf_demo_atom lbg_demo_row_code (fun _ : nat => 0)). Qed.

(* 展品二（端到端往返）：编码 → 解码重演恰回 Σ-原子——
   lbg_gnPrf2_replay 实例：第一张码级证书化凭证的码经 dPrf2 自燃料重演，
   恰为 fsig (numT 3000) (numT ⌜teq 0 0⌝)。 *)
Theorem lbg_demo_row_code_replay :
  loeb_tid (option Formula2)
    (dPrf2 (gnPrf2 lbf_demo_atom lbg_demo_row_code)
           (gnPrf2 lbf_demo_atom lbg_demo_row_code))
    (Some lbf_demo_atom).
Proof.
  exact (lbg_gnPrf2_replay lbf_demo_atom lbg_demo_row_code
    (gnPrf2 lbf_demo_atom lbg_demo_row_code) (Nat.le_refl _)).
Qed.

(* —— 假设面自审（全部应 Closed under the global context） —— *)
Print Assumptions lbg_dPrf2_fuel_inv.
Print Assumptions lbg_gnPrf2_replay.
Print Assumptions lbg_dPrf2_gnPrf_none.
Print Assumptions lbg_dPrf2_lbe_gnF2_none.
Print Assumptions lbg_MPc2_code_closed.
Print Assumptions lbg_Box2_HBL1.
Print Assumptions lbg_Box2_HBL3.
Print Assumptions lbg_prf2_repl_code.
Print Assumptions lbg_prf2_sig_code.
Print Assumptions lbg_demo_row_code_sound.
Print Assumptions lbg_demo_row_code_replay.
