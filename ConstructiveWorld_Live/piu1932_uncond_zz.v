(* piu1932_uncond_zz.v —— Route B 装配正件（真实件名版）
   溯源: K01 v1 工艺（shot2d apply 型 transport 绿证）+ M02 v2 命名律
   实例化: C0 := piu_zz_C0 = 1/10^9（bridge_real:60 折半换算锚，
     piu_zz_halving_chain 钉 2·C₀ < c₀_criterion = 1/71663616 = t⁷/2⁸）;
     alpha := 8（字面；ZZ 记录 μ=1+σ/τ≈7.1032 < 8，对拍组 B 机械背书）。
   诚实接口申报（红线律口径）: 唯一前提 = 率面 μ 证书（real_lt=sigT，
     Set 承载），出节即定理显式函数参数（K01 mock 判例同款）; 「uncond」
     名实 = Route B 消灭 cwin 死槽 HC0_valid（E01 §2.0 判定数学不可满足），
   使命: Route B 装配正件——率面 μ 证书驱动的一致型紧上界无条件化实例。
   依赖清单: S01/S02/S03/S10/PiEnvelope/LW0MLicBridge/LW1PiMeasure/tlw1448_rebase/tlw1448_transfer/tlw1703_unif_tight_instantiation/piu1932_tight_bound_instantiated/piu_zz_bridge_real/piu_zz_bridge_rateslot/piu_zz_constants。
   构造性注记: 零 Axiom/Admitted/Parameter/Conjecture/Abort；唯一前提=率面 μ 证书（Set 承载）。
   编译配方: 依赖件先行后 rocq c -native-compiler no -q -Q . "" piu1932_uncond_zz.v
     非零前提; P2③+P1 实装后沿 bridge_real 头注既定链 discharge。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.  (* Qabs 函数族＋
   Qceiling/Qfloor 名源（发7 复核: probe3=+Qround Check 过·probe4=Qring 单独红——
   Qring 无关，真源=Qround；同族缺口第六处·tlw1703:27/mock 判例头部逐字同款） *)
(* Require 头=K01 _probe_routeB_mock 绿证判例逐字（发1 实测: Require Import
   非传递导出——rateslot 帧内 S02/LW1M/tlw1448 等裸名不随 Require 供出，
   K02 §二三行处方漏此 Import 传递缺口，本件按 K01 判例全链显式补齐，
   语句面零改动；M02 烟测 22 项 Check 唯一解析背书单源无歧义） *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.                (* real_lt/real_const/real_metric 面 *)
Require Import S03_QExp.
Require Import S10_KVQuantTrig.                   (* real_pi_geom（发3 实测补·同族缺口第三处） *)
Require Import PiEnvelope.                        (* QltT'/QltT_to_Qlt/Qlt_to_QltT' *)
Require Import LW0MLicBridge.
Require Import LW1PiMeasure.                      (* lw1m_height/lw1m_dist_pt/lw1m_snq_pos *)
Require Import tlw1448_rebase.                    (* tlw1448_nsep_rebase *)
Require Import tlw1448_transfer.                  (* tlw1448_ck *)
Require Import tlw1703_unif_tight_instantiation.  (* rebase_le_Sbpowc/bpow_c/nsep_rebase 面 *)
Require Import piu1932_tight_bound_instantiated.  (* ck_alpha/div_pos/qleT'_refl 面 *)
Require Import piu_zz_bridge_real.                (* 基件 18 名（C0/C0_pos/c0_criterion 等）：
                                                     发2 实测 Import 非传递同族缺口——
                                                     rateslot 头注「随链带入」仅 .vo 加载层，
                                                     名不随 Require Import rateslot 供出；
                                                     M02 已废止禁双 Require 条款（同名单源
                                                     解析无歧义），v2 名照单不退 *)
Require Import piu_zz_bridge_rateslot.            (* v2 名唯一供体（M02 §三） *)
Require Import piu_zz_constants.                  (* 对拍组 B/C 数值面 *)

(* E345 律: 发前 vernacular 检查 —— 与 K01 shot1 钉定形比对，
   漂移即停发响亮登记（K02 §三 F1）。 *)
Check tlw1703_unif_rebase_le_Sbpowc.

Section Piu1932Instantiation.   (* 契约件同名 Section 非冲突源（M02 #24 判例）*)

Theorem piu1932_uncond_zz :
  (forall q : Q, (0 < q)%Q ->
     real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
             (real_metric real_pi_geom (real_const q))) ->
  forall q : Q,
    NatLe (tlw1448_nsep_rebase tlw1448_ck q)
          (Datatypes.S (tlw1703_unif_bpow_c piu_zz_C0 8 (lw1m_height q))).
Proof.
  intros Hmu q.
  apply (tlw1703_unif_rebase_le_Sbpowc piu_zz_C0 8 (piu1932_ck_alpha piu_zz_C0 8)).
  - (* 槽1 HC0_pos: QltT' 0 piu_zz_C0 —— 池件直供（v2 免 v1 字面 lia） *)
    exact piu_zz_C0_pos.
  - (* 槽2 Hcrt_pos: forall q', QltT' 0 (ck_alpha C0 8 q') —— K01 mock 逐字 *)
    intros q'. apply piu1932_div_pos.
    + exact (QltT_to_Qlt _ _ piu_zz_C0_pos).
    + apply Qlt_to_QltT'. apply tlw1703_unif_qpow_pos.
      exact (QltT_to_Qlt _ _
               (lw1m_snq_pos (Pos.to_nat (Qden (Qred q'))))).
  - (* 槽3 Hcrt_dist —— v2 压缩点: v1 三行 transport+双占位槽 → 池件一步 *)
    intros q'. exact (piu_zz_bridge_full_v2 Hmu q').
  - (* 槽4 Hcert_pow: crt:=ck_alpha 自反（Route B β 不使用点·E01 §2.3） *)
    intros q'. apply piu1932_qleT'_refl.
Qed.

End Piu1932Instantiation.

(* ============================================================ *)
(* §5 终检: G4 假设审计（五名）                                     *)
(* ============================================================ *)

Print Assumptions piu1932_uncond_zz.
Print Assumptions piu_zz_bridge_full_v2.
Print Assumptions piu_zz_bridge_nonpos.
Print Assumptions piu_zz_C0_pos.
Print Assumptions tlw1703_unif_rebase_le_Sbpowc.

(* ============================================================ *)
(* §四 对拍样点组 A/B/C（单件内单发编译·零额外发数）                   *)
(* ============================================================ *)

(* 组 A（停点形·3 样点·精确整数账: 8/C₀ = 8·10⁹ 整数 ⟹ 天花板零舍入）
   发4 实测修正: K02 §四 nat 字面 vm_compute 形在 h=2 即 2×10¹² unary
   构造子求值必爆（K02 零编译盲点·fail-loud 登记）——按 K01
   probe_routeB_stop_shape 判例工艺改两组闭合：
   ①停点展开形 reflexivity 转换核验（全称 h·零大数求值·K01 逐字同款）；
   ②三样点数值账以 Qceiling 的 Z 载体 vm_compute（binary 可行），
   8/C₀=8·10⁹ 精确整数账实质不变。 *)
Example piu1932_uncond_zz_stop_shape : forall h : nat,
  Datatypes.S (tlw1703_unif_bpow_c piu_zz_C0 8 h) =
  Datatypes.S (Datatypes.S
    (Z.to_nat (Qceiling ((8 / piu_zz_C0 * q_pow (Z.of_nat h # 1) 8)%Q)))).
Proof. reflexivity. Qed.

Example piu1932_uncond_zz_stop_h2  :
  Qceiling ((8 / piu_zz_C0 * q_pow (Z.of_nat 2 # 1) 8)%Q) = 2048000000000%Z.
Proof. vm_compute. reflexivity. Qed.  (* 即定理停点 2048000000002 = 8e9·2^8+2 *)
Example piu1932_uncond_zz_stop_h3  :
  Qceiling ((8 / piu_zz_C0 * q_pow (Z.of_nat 3 # 1) 8)%Q) = 52488000000000%Z.
Proof. vm_compute. reflexivity. Qed.  (* 8e9·3^8 = 52488000000000 *)
Example piu1932_uncond_zz_stop_h10 :
  Qceiling ((8 / piu_zz_C0 * q_pow (Z.of_nat 10 # 1) 8)%Q) = 800000000000000000%Z.
Proof. vm_compute. reflexivity. Qed.  (* 8e9·10^8 = 8e17 *)

(* 组 B（μ 夹逼对拍·constants 件）: 7.103205334138 < 8 = 实例化指数。
   诚实边界: 只证指数兼容性，不证 Hmu 证书本身（距离下界供给=P2③+判据实装，
   非本切片）。 *)
Example piu1932_uncond_zz_alpha_guard :
  zzQltT piu_zzc_mu_zz_upper (8 # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* 组 C（C₀ 折半对拍·桥型引理）: 2e-9 < 1.3954e-8 *)
Example piu1932_uncond_zz_halving_view :
  zzQltT ((2 # 1) * piu_zz_C0)%Q piu_zz_c0_criterion.
Proof. vm_compute. exact tt. Qed.

(* ============================================================ *)
(* G3 提取小名单（≤6·禁列证明重名入大名单——A02 提取病卡）               *)
(* ============================================================ *)

Extraction "piu1932_uncond_zz_ext" piu1932_uncond_zz tlw1703_unif_bpow_c piu_zz_bridge_full_v2.
