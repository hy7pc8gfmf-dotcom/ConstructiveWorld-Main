# -*- coding: utf-8 -*-
"""CW219 基座分片生成器：字节级纯切割 + 头部补齐。

红线保证：分片正文 = 基座原文连续行区间的原始字节（含 CRLF），
仅首部追加机械生成的头部（头部行数记录于头部注释，供机械验证）。
验收：tools/verify_split.py 去头拼接 ≡ 原文逐字节。
"""
import io, sys, os

BASE = r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo\CW_ConstructiveWorld_219.v"
OUTDIR = r"D:\ComplexAnalysis\ConstructiveWorld-Main\CW219_split"

SHARDS = [
    ("S01_BaseRing",          1,   3071),
    ("S02_CauchyComplete",    3072,  6982),
    ("S03_QExp",              6983, 13800),
    ("S04_RealExpLogConv",   13801, 18733),
    ("S05_AlignmentGRPO",    18734, 24767),
    ("S06_DiffSamplingGibbs",24768, 32574),
    ("S07_RealSetoidExpLog", 32575, 41232),
    ("S08_RealMainlineDPO",  41233, 46820),
    ("S09_EntropyReal",      46821, 53931),
    ("S10_KVQuantTrig",      53932, 66414),
    ("S11_TP3B5",            66415, 79152),
    ("S12_B5RecycleSF",      79153, 93447),
    ("S13_NLiveAudit",       93448, 97866),
    ("S14_B5BatchBlock",     97867, 112163),
    ("S15_TailFEPUp",       112164, 114222),
]

CRLF = "\r\n"

def shard_header(idx, name, a, b):
    """idx: 0-based shard index; a..b: 1-based inclusive source line range."""
    if idx == 0:
        return []  # S01 = 原文 L1-3071 逐字节，零头部
    L = []
    L.append("(* ===== CW219 拆分分片 %s（机械生成头部，非原文） ===== *)" % name)
    L.append("(* 原文区间：ConstructiveWorld_vo/CW_ConstructiveWorld_219.v L%d-L%d；" % (a, b))
    L.append("   本头部共 %d 行；去头后正文 ≡ 原文该区间逐字节（tools/verify_split.py 可验） *)" % 0)  # 占位，稍后回填
    return L  # 占位：真实生成见 build()

def build():
    with io.open(BASE, 'rb') as f:
        raw = f.read()
    # 按 \n 切（保留行内 \r），保持原始字节
    pieces = raw.split(b"\n")
    # pieces[i] = 第 i+1 行内容（不含 \n）；文件以 \n 结尾时最后一片为空
    n_lines = len(pieces) - 1 if pieces[-1] == b"" else len(pieces)
    assert n_lines == 114222, n_lines

    for idx, (name, a, b) in enumerate(SHARDS):
        body = b"\n".join(pieces[a-1:b])
        if b < n_lines:
            body += b"\n"
        if idx == 0:
            content = body
            hdr_lines = 0
        else:
            deps = " ".join("S%02d" % (i+1) for i in range(idx))
            hl = []
            hl.append("(* ===== CW219 拆分分片 %s（机械生成头部，非原文） ===== *)" % name)
            hl.append("(* 原文区间：CW_ConstructiveWorld_219.v L%d-L%d；头部 %d 行（回填）；" % (a, b, 0))
            hl.append("   依赖：%s；去头正文 ≡ 原文区间逐字节（tools/verify_split.py） *)" % deps)
            for i in range(idx):
                hl.append("Require Import S%02d_%s." % (i+1, SHARDS[i][0].split("_", 1)[1]))
            # 外部 Require（复现原文 L54-58）
            hl.append("From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround")
            hl.append("               Lists.List Bool.Bool Arith.Arith.")
            hl.append("Import ListNotations.")
            hl.append("From Stdlib Require Import Setoid Morphisms.")
            hl.append("From Stdlib Require Import Lia QArith.Qminmax.")
            # 状态重放
            if idx >= 4:   # S05+（原文 L15519 < 本片起始）
                hl.append("Import PropositionConvergenceCore.")
            if idx >= 11:  # S12+（原文 L78208 < 本片起始 79153）
                hl.append("From Stdlib Require Import Psatz.")
            if idx >= 14:  # S15（原文 L95607 < 本片起始）
                hl.append("From Stdlib Require Import ZArith.Znat.")
            if idx >= 7:   # S08+（原文 L33494 < 本片起始）
                hl.append("Opaque Qred.")
            # 回填头部行数（含头部空行 1 行）
            hdr_lines = len(hl) + 1
            hl[1] = hl[1].replace("头部 0 行（回填）", "头部 %d 行（含尾空行）" % hdr_lines)
            header = (CRLF.join(hl) + CRLF + CRLF).encode("utf-8")
            content = header + body
        outp = os.path.join(OUTDIR, name + ".v")
        with io.open(outp, "wb") as g:
            g.write(content)
        print("%s.v  body=L%d-L%d (%d lines)  header=%d lines  total=%d bytes"
              % (name, a, b, b - a + 1, hdr_lines, len(content)))

if __name__ == "__main__":
    build()
