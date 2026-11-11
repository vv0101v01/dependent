# Module M10：`m10_affine_quant_types`（仿射與量化依賴類型論 QTT、64-bit SWAR 資源遮罩與零階抹除）

本模組為獨立基礎模組（零跨模組依賴），涵蓋附件二之 **仿射與量化類型（Affine & Quantitative Type Theory, QTT）**，結合 McBride (2016)、Atkey (LICS 2018 / POPL 2024)、Šefl & Svoboda 加性量化對與 Eriksson-Danielsson-Abel (TYPES 2025) 伽羅瓦殘差半環理論，將 32 個語境變數之資源重數壓縮於單一 64-bit 硬體暫存器字組 `UsageVec64` 中，同時支援嚴格線性（`1`）、仿射（`<=1`）、零階擦除（`0`）與無限制（`ω`）依賴類型檢驗及認證零階執行期抹除。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **全域公理 M10.A1（有序資源半環與伽羅瓦殘差減法公理）**：四元資源半環 $\mathcal{Q} = \{0, 1, \le\!1, \omega\}$ 配備乘法張量加法 $+$、語境縮放乘法 $\cdot$、加性分支聯集 $\sqcup$（滿足 $1 \sqcup 1 = 1, 1 \sqcup 0 = {\le\!1}$）與供給包攝偏序 $\preceq$；殘差減法 `Grade::residuated_sub(budget, already)` 精確求得滿足 $(\text{already} + r) \preceq \text{budget}$ 之最小剩餘需求階 $r$（超額時返回 `None`）。
2. **定理 M10.T1（McBride-Atkey 零階依賴類型形成自由定理）**：類型形成判斷 $0 \cdot \Gamma \vdash A\ \mathsf{Type}$ 將全部類型內部變數使用量乘以 $0$（`UsageVec64::scale(GZero) == 0UL`），使嚴格線性或仿射變數可於依賴相等類型 `Id(A, x, y)` 與規格中任意出現而不消耗執行期配額，同時嚴格阻斷執行期直接洩漏零階變數（`ZeroGradeVariableUsedAtRuntime`）。
3. **定理 M10.T2（乘性張量配對 $\Sigma_\pi$ 與加性笛卡兒配對 $A \with B$ 對偶區隔定理）**：乘性張量配對累加資源向量 $\pi \cdot \vec{u}_1 + \vec{u}_2$（故仿射變數禁止於 `x ⊗^1 x` 中複製），而加性配對 `QWithPair` 採惰性分支共享 $\vec{u}_1 \sqcup \vec{u}_2$（故嚴格線性變數可合法構造對角加性配對 `⟨x, x⟩_&`）。
4. **定理 M10.T3（認證零階執行期抹除健全性定理）**：`erase_qtt_term` 將所有零階函數抽象 `λ(x :^0 A). e`、零階應用 `f @^0 a`、零階張量首分量與相等性證明項完全抹除為無開銷無類型執行期核心項 `RuntimeTerm`。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 四元仿射—量化半環與伽羅瓦殘差器 (`Grade::{add, mul, additive_join, subsumed_by, residuated_sub}`) | `grade_semiring_swar.mbt` | $O(1)$ | 2-bit 編碼統一表達擦除、線性、仿射與無限制重數 |
| 64-bit SWAR 資源向量平行運算器 (`UsageVec64::{singleton, get, clear_slot, scale, add, additive_join}`) | `grade_semiring_swar.mbt` | $O(1)$ 暫存器級運算 | 單一 `UInt64` 封裝 32 變數重數；零階縮放與互斥變數集加法均為單條位元指令快篩 |
| 量化依賴類型正規化與雙向資源檢驗器 (`normalize_qterm`, `check_qtype`, `synth_qterm_raw`, `verify_qtt_judgment`) | `qtt_checker_erasure.mbt` | 多項式於項規模 | 精確檢驗 $\Pi_\pi, \Sigma_\pi, A \with B, \mathsf{If}, \mathsf{Id}$ 之局部與全局資源包攝 |
| 認證零階執行期抹除編譯器 (`erase_qtt_term`) | `qtt_checker_erasure.mbt` | $O(\|t\|)$ | 剝離所有編譯期類型參數與規格憑證 |

---

## 三、資料夾視角的依賴關係圖

```text
                  [ 外部上游依賴：無（純獨立基礎模組） ]
                                    │
                                    ▼
             ┌─────────────────────────────────────────────┐
             │          dtt/m10_affine_quant_types         │
             │        grade_semiring_swar.mbt              │
             │        qtt_checker_erasure.mbt              │
             └──────────────────────┬──────────────────────┘
                                    │
                                    ▼
                     [ dtt/m13_qtt_elaboration_bridge ]
                                    │
                                    ▼
                    [ dtt/m14_phase2_unified_system ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `grade_semiring_swar.mbt` 提供 2-bit 資源半環 `Grade` 與 64-bit 壓縮向量 `UsageVec64`。
2. `qtt_checker_erasure.mbt` 在 `UsageVec64` 之上實作雙向依賴類型與資源合成器 `verify_qtt_judgment`，並由 `erase_qtt_term` 編譯至執行期目標碼 `RuntimeTerm`。

### 輸出公共接口（Public API）
- **類型與錯誤**：`Grade`, `UsageVec64`, `QTerm`, `QCtxEntry`, `RuntimeTerm`, `QTTError`。
- **核心函式**：`Grade::{to_bits, from_bits, add, mul, additive_join, subsumed_by, residuated_sub}`, `UsageVec64::{zero, singleton, get, clear_slot, scale, add, additive_join}`, `shift_qterm`, `subst_qterm`, `normalize_qterm`, `check_qtype`, `synth_qterm_raw`, `check_qterm_raw`, `verify_qtt_judgment`, `erase_qtt_term`。
