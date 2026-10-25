(* piu_zz_tau_hb_wave4a.v — KB11 Hb 升格候选子片 4/8（1024 段 Hb16-Hb31·机械升格件·零漂移回读断言已过）。
   [KB20 checkpoint split] 本件=wave4（1024_16..31 重条区）四等分 a/4；引理自 wave4 逐字搬移，语句/体零改写。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave4.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
(* src piu_zz_tau_enclosure.v L1355-L1375 (assert Hb16) *)
Lemma piu_zz_hb_1024_16 : piu_zz_zprod_seg 1024%nat (512%nat + 1264%nat) 16%nat = ((if zz_in_Pn 1024 1777%nat then Z.of_nat 1777%nat else 1%Z) * ((if zz_in_Pn 1024 1778%nat then Z.of_nat 1778%nat else 1%Z) * ((if zz_in_Pn 1024 1779%nat then Z.of_nat 1779%nat else 1%Z) * ((if zz_in_Pn 1024 1780%nat then Z.of_nat 1780%nat else 1%Z) * ((if zz_in_Pn 1024 1781%nat then Z.of_nat 1781%nat else 1%Z) * ((if zz_in_Pn 1024 1782%nat then Z.of_nat 1782%nat else 1%Z) * ((if zz_in_Pn 1024 1783%nat then Z.of_nat 1783%nat else 1%Z) * ((if zz_in_Pn 1024 1784%nat then Z.of_nat 1784%nat else 1%Z) * ((if zz_in_Pn 1024 1785%nat then Z.of_nat 1785%nat else 1%Z) * ((if zz_in_Pn 1024 1786%nat then Z.of_nat 1786%nat else 1%Z) * ((if zz_in_Pn 1024 1787%nat then Z.of_nat 1787%nat else 1%Z) * ((if zz_in_Pn 1024 1788%nat then Z.of_nat 1788%nat else 1%Z) * ((if zz_in_Pn 1024 1789%nat then Z.of_nat 1789%nat else 1%Z) * ((if zz_in_Pn 1024 1790%nat then Z.of_nat 1790%nat else 1%Z) * ((if zz_in_Pn 1024 1791%nat then Z.of_nat 1791%nat else 1%Z) * (if zz_in_Pn 1024 1792%nat then Z.of_nat 1792%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1792.
    rewrite piu_zz_inPn_1024_1791.
    rewrite piu_zz_inPn_1024_1790.
    rewrite piu_zz_inPn_1024_1789.
    rewrite piu_zz_inPn_1024_1788.
    rewrite piu_zz_inPn_1024_1787.
    rewrite piu_zz_inPn_1024_1786.
    rewrite piu_zz_inPn_1024_1785.
    rewrite piu_zz_inPn_1024_1784.
    rewrite piu_zz_inPn_1024_1783.
    rewrite piu_zz_inPn_1024_1782.
    rewrite piu_zz_inPn_1024_1781.
    rewrite piu_zz_inPn_1024_1780.
    rewrite piu_zz_inPn_1024_1779.
    rewrite piu_zz_inPn_1024_1778.
    rewrite piu_zz_inPn_1024_1777.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1376-L1396 (assert Hb17) *)
Lemma piu_zz_hb_1024_17 : piu_zz_zprod_seg 1024%nat (512%nat + 1248%nat) 16%nat = ((if zz_in_Pn 1024 1761%nat then Z.of_nat 1761%nat else 1%Z) * ((if zz_in_Pn 1024 1762%nat then Z.of_nat 1762%nat else 1%Z) * ((if zz_in_Pn 1024 1763%nat then Z.of_nat 1763%nat else 1%Z) * ((if zz_in_Pn 1024 1764%nat then Z.of_nat 1764%nat else 1%Z) * ((if zz_in_Pn 1024 1765%nat then Z.of_nat 1765%nat else 1%Z) * ((if zz_in_Pn 1024 1766%nat then Z.of_nat 1766%nat else 1%Z) * ((if zz_in_Pn 1024 1767%nat then Z.of_nat 1767%nat else 1%Z) * ((if zz_in_Pn 1024 1768%nat then Z.of_nat 1768%nat else 1%Z) * ((if zz_in_Pn 1024 1769%nat then Z.of_nat 1769%nat else 1%Z) * ((if zz_in_Pn 1024 1770%nat then Z.of_nat 1770%nat else 1%Z) * ((if zz_in_Pn 1024 1771%nat then Z.of_nat 1771%nat else 1%Z) * ((if zz_in_Pn 1024 1772%nat then Z.of_nat 1772%nat else 1%Z) * ((if zz_in_Pn 1024 1773%nat then Z.of_nat 1773%nat else 1%Z) * ((if zz_in_Pn 1024 1774%nat then Z.of_nat 1774%nat else 1%Z) * ((if zz_in_Pn 1024 1775%nat then Z.of_nat 1775%nat else 1%Z) * (if zz_in_Pn 1024 1776%nat then Z.of_nat 1776%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1776.
    rewrite piu_zz_inPn_1024_1775.
    rewrite piu_zz_inPn_1024_1774.
    rewrite piu_zz_inPn_1024_1773.
    rewrite piu_zz_inPn_1024_1772.
    rewrite piu_zz_inPn_1024_1771.
    rewrite piu_zz_inPn_1024_1770.
    rewrite piu_zz_inPn_1024_1769.
    rewrite piu_zz_inPn_1024_1768.
    rewrite piu_zz_inPn_1024_1767.
    rewrite piu_zz_inPn_1024_1766.
    rewrite piu_zz_inPn_1024_1765.
    rewrite piu_zz_inPn_1024_1764.
    rewrite piu_zz_inPn_1024_1763.
    rewrite piu_zz_inPn_1024_1762.
    rewrite piu_zz_inPn_1024_1761.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1397-L1417 (assert Hb18) *)
Lemma piu_zz_hb_1024_18 : piu_zz_zprod_seg 1024%nat (512%nat + 1232%nat) 16%nat = ((if zz_in_Pn 1024 1745%nat then Z.of_nat 1745%nat else 1%Z) * ((if zz_in_Pn 1024 1746%nat then Z.of_nat 1746%nat else 1%Z) * ((if zz_in_Pn 1024 1747%nat then Z.of_nat 1747%nat else 1%Z) * ((if zz_in_Pn 1024 1748%nat then Z.of_nat 1748%nat else 1%Z) * ((if zz_in_Pn 1024 1749%nat then Z.of_nat 1749%nat else 1%Z) * ((if zz_in_Pn 1024 1750%nat then Z.of_nat 1750%nat else 1%Z) * ((if zz_in_Pn 1024 1751%nat then Z.of_nat 1751%nat else 1%Z) * ((if zz_in_Pn 1024 1752%nat then Z.of_nat 1752%nat else 1%Z) * ((if zz_in_Pn 1024 1753%nat then Z.of_nat 1753%nat else 1%Z) * ((if zz_in_Pn 1024 1754%nat then Z.of_nat 1754%nat else 1%Z) * ((if zz_in_Pn 1024 1755%nat then Z.of_nat 1755%nat else 1%Z) * ((if zz_in_Pn 1024 1756%nat then Z.of_nat 1756%nat else 1%Z) * ((if zz_in_Pn 1024 1757%nat then Z.of_nat 1757%nat else 1%Z) * ((if zz_in_Pn 1024 1758%nat then Z.of_nat 1758%nat else 1%Z) * ((if zz_in_Pn 1024 1759%nat then Z.of_nat 1759%nat else 1%Z) * (if zz_in_Pn 1024 1760%nat then Z.of_nat 1760%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1760.
    rewrite piu_zz_inPn_1024_1759.
    rewrite piu_zz_inPn_1024_1758.
    rewrite piu_zz_inPn_1024_1757.
    rewrite piu_zz_inPn_1024_1756.
    rewrite piu_zz_inPn_1024_1755.
    rewrite piu_zz_inPn_1024_1754.
    rewrite piu_zz_inPn_1024_1753.
    rewrite piu_zz_inPn_1024_1752.
    rewrite piu_zz_inPn_1024_1751.
    rewrite piu_zz_inPn_1024_1750.
    rewrite piu_zz_inPn_1024_1749.
    rewrite piu_zz_inPn_1024_1748.
    rewrite piu_zz_inPn_1024_1747.
    rewrite piu_zz_inPn_1024_1746.
    rewrite piu_zz_inPn_1024_1745.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1418-L1438 (assert Hb19) *)
Lemma piu_zz_hb_1024_19 : piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) 16%nat = ((if zz_in_Pn 1024 1729%nat then Z.of_nat 1729%nat else 1%Z) * ((if zz_in_Pn 1024 1730%nat then Z.of_nat 1730%nat else 1%Z) * ((if zz_in_Pn 1024 1731%nat then Z.of_nat 1731%nat else 1%Z) * ((if zz_in_Pn 1024 1732%nat then Z.of_nat 1732%nat else 1%Z) * ((if zz_in_Pn 1024 1733%nat then Z.of_nat 1733%nat else 1%Z) * ((if zz_in_Pn 1024 1734%nat then Z.of_nat 1734%nat else 1%Z) * ((if zz_in_Pn 1024 1735%nat then Z.of_nat 1735%nat else 1%Z) * ((if zz_in_Pn 1024 1736%nat then Z.of_nat 1736%nat else 1%Z) * ((if zz_in_Pn 1024 1737%nat then Z.of_nat 1737%nat else 1%Z) * ((if zz_in_Pn 1024 1738%nat then Z.of_nat 1738%nat else 1%Z) * ((if zz_in_Pn 1024 1739%nat then Z.of_nat 1739%nat else 1%Z) * ((if zz_in_Pn 1024 1740%nat then Z.of_nat 1740%nat else 1%Z) * ((if zz_in_Pn 1024 1741%nat then Z.of_nat 1741%nat else 1%Z) * ((if zz_in_Pn 1024 1742%nat then Z.of_nat 1742%nat else 1%Z) * ((if zz_in_Pn 1024 1743%nat then Z.of_nat 1743%nat else 1%Z) * (if zz_in_Pn 1024 1744%nat then Z.of_nat 1744%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1744.
    rewrite piu_zz_inPn_1024_1743.
    rewrite piu_zz_inPn_1024_1742.
    rewrite piu_zz_inPn_1024_1741.
    rewrite piu_zz_inPn_1024_1740.
    rewrite piu_zz_inPn_1024_1739.
    rewrite piu_zz_inPn_1024_1738.
    rewrite piu_zz_inPn_1024_1737.
    rewrite piu_zz_inPn_1024_1736.
    rewrite piu_zz_inPn_1024_1735.
    rewrite piu_zz_inPn_1024_1734.
    rewrite piu_zz_inPn_1024_1733.
    rewrite piu_zz_inPn_1024_1732.
    rewrite piu_zz_inPn_1024_1731.
    rewrite piu_zz_inPn_1024_1730.
    rewrite piu_zz_inPn_1024_1729.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
