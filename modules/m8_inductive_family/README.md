# Module M8：`m8_inductive_family`（嚴格正歸納類型、巢狀稀疏參數化、歸納-遞歸類型與歸納-歸納類型）

本模組為獨立基礎模組（零跨模組依賴），涵蓋附件二之 **嚴格正歸納類型（Strictly Positive Inductive Types）**、**歸納-遞歸類型（Inductive-Recursive Types, IR）** 與 **歸納-歸納類型（Inductive-Inductive Types, II）**，結合 POPL/ICFP 2026 巢狀嚴格正參數稀疏參數化理論（`10.1145/3808322`）、Dybjer-Setzer 同時編解碼演算、Forsberg-Kaposi 內在伸縮語法與多項式容器 $W$-始代數摺疊。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **公理 M8.A1（嚴格正性與 Cantor-Girard 悖論阻斷公理）**：歸納類型 $I$ 於建構子參數 $T$ 中嚴格正出現，當且僅當 $I$ 絕不出現在任何函數箭頭左側（即使雙重否定 $((I \to \mathbf{0}) \to \mathbf{0}) \to I$ 在極性代數中為正 `Positive`，仍非嚴格正 `StrictlyPositive`），亦不出現在自身索引或非嚴格正巢狀容器槽位中。
2. **定理 M8.T1（巢狀歸納類型稀疏參數化與 64 位元遮罩保持定理）**：對任意通過 `check_strict_positivity` 驗證之歸納宣告，`sp_param_mask` 的第 $p$ 位元為 $1 \iff$ 類型參數 $\alpha_p$ 在所有建構子中皆為 `Unused` 或 `StrictlyPositive`；僅需對 `rec_arg_mask` 標記之建構子參數生成稀疏歸納假設（常數參數零額外假設）。
3. **定理 M8.T2（Dybjer-Setzer 歸納-遞歸同時初始代數解碼定理）**：泛型編碼 `IRCode[D]`（含 $\iota(d)$、$\sigma(k, f)$ 與高階依賴分支 $\delta(k, \Phi \circ T)$）與封閉 Tarski 宇宙 `IRUni`（含 `UFin`、`USigmaIR`、`UPiIR`）在同一遞歸週期內同時驗證後續欄位對前序欄位解碼基數 $|El(a)|$ 之依賴並計算總基數（$\Sigma \mapsto \sum_i |B_i|, \Pi \mapsto \prod_i |B_i|$）。
4. **定理 M8.T3（Forsberg-Kaposi 歸納-歸納互鎖良構與遞歸-遞歸消元定理）**：基底類 `IICtx` 與索引族 `IITy : IICtx -> Set`（其中 `IISnoc` 引用 `IITy`，而 `IIPi`/`IISigma` 之餘域索引引用 `IISnoc`）具備互鎖良構可判定性，且遞歸-遞歸消元器 `ii_elim_ctx` / `ii_elim_ty` 構成始代數唯一態射。
5. **定理 M8.T4（多項式容器 $W$-始代數摺疊良基定理）**：任意有限分支容器樹 `WTree[S]` 上之始代數摺疊 `cata_w` 嚴格良基終止，其 Brouwer 樹高秩嚴格單調遞減。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 極性晶格運算與雙重否定區隔器 (`ParamPolarity::join`, `negate_left_of_arrow`) | `sp_polarity.mbt` | $O(1)$ | 嚴格區分 `StrictlyPositive` 與雙重否定產生之 `Positive` |
| 64-bit 嚴格正性與巢狀容器檢驗器 (`check_strict_positivity`) | `sp_polarity.mbt` | $O(\sum \|T_i\| \cdot P)$ | 合成 64-bit `sp_param_mask`、`rec_arg_mask`、`nested_rec_mask` 與 $O(1)$ 葉建構子判定 `is_leaf` |
| Dybjer-Setzer 泛型 IR 解碼器與封閉宇宙基數器 (`ir_decode_with_root`, `ir_check_and_decode_card`) | `ir_ii_containers.mbt` | $O(\|\text{tree}\|)$ | 同步執行依賴良構驗證與遞歸語義解碼 |
| 歸納-歸納互鎖檢驗與遞歸-遞歸消元器 (`check_ii_ctx`, `check_ii_ty`, `ii_elim_ctx`, `ii_elim_ty`) | `ir_ii_containers.mbt` | $O(\|\Gamma\| + \|T\|)$ | 在餘域消元時自動注入 `on_snoc(cg, ta)` 語義擴張 |
| 容器 $W$-樹始代數摺疊器 (`cata_w`, `w_tree_height`) | `ir_ii_containers.mbt` | $O(\|W\|)$ | 泛型多項式容器始代數態射 |

---

## 三、資料夾視角的依賴關係圖

```text
                  [ 外部上游依賴：無（純獨立基礎模組） ]
                                    │
                                    ▼
             ┌─────────────────────────────────────────────┐
             │          dtt/m8_inductive_family            │
             │       sp_polarity.mbt                       │
             │       ir_ii_containers.mbt                  │
             └──────────────────────┬──────────────────────┘
                                    │
                                    ▼
                     [ dtt/m12_initial_final_duality ]
                                    │
                                    ▼
                    [ dtt/m14_phase2_unified_system ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `sp_polarity.mbt` 驗證歸納宣告之嚴格正性與巢狀容器相容性，輸出 64-bit 位元摘要憑證 `CertifiedInductiveSummary`。
2. `ir_ii_containers.mbt` 實作 IR 同時編解碼、II 互鎖語法檢驗與遞歸-遞歸消元，以及容器 $W$-樹摺疊。

### 輸出公共接口（Public API）
- **類型與錯誤**：`ParamPolarity`, `SPTypeExpr`, `InductiveCtorDecl`, `InductiveDecl`, `CertifiedCtorSummary`, `CertifiedInductiveSummary`, `IRCode`, `IRNode`, `IRUni`, `IICtx`, `IITy`, `WTree`, `InductiveError`。
- **核心函式**：`ParamPolarity::{join, negate_left_of_arrow}`, `CertifiedCtorSummary::is_leaf`, `check_strict_positivity`, `ir_decode_generic`, `ir_decode_with_root`, `ir_check_and_decode_card`, `ii_ty_ctx`, `check_ii_ctx`, `check_ii_ty`, `ii_elim_ctx`, `ii_elim_ty`, `cata_w`, `w_tree_height`。
