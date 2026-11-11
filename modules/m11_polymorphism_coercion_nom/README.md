# Module M11：`m11_polymorphism_coercion_nom`（依賴多型性、隱含參數重寫與模式合一、型別強制轉換、結構型別與名義型別）

本模組為獨立基礎模組（零跨模組依賴），涵蓋附件二之 **依賴多型性（Dependent Polymorphism）**、**隱含參數重寫（Implicit Argument Elaboration & Rewriting）**、**型別強制轉換（Coercive Subtyping & Coherence）** 與 **結構型別與名義型別（Structural vs Nominal Typing）**，結合 Miller-Abel-Pientka 高階模式合一與脊修剪（Spine Pruning）、Knuth-Bendix 遞減權重隱含重寫、Luo-Laurent-Najmaei (2024 / POPL 2026) 菱形相干強制子型別，以及 WasmGC 級 64-bit Popcount $O(1)$ 稀疏結構紀錄與生成式名義品牌隔離。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **定理 M11.T1（依賴多型方案隱含實例化與二元關係參數化定理）**：宇宙與隱含依賴伸縮方案 `DepPolyScheme` 在任意語境深度 $d$ 下自動插入線性脊元變數 `?m[d-1, ..., 0]`，其二元關係參數化維度嚴格滿足 $3 n_{\mathrm{ty}} + 3 n_{\mathrm{val}}$。
2. **定理 M11.T2（Knuth-Bendix 權重遞減隱含重寫強終止與模重寫 Miller 模式合一定理）**：滿足 $\mathrm{weight}(\mathrm{lhs}) > \mathrm{weight}(\mathrm{rhs})$ 且無變數倍增之規則集必有限終止；`unify_modulo_rewrites` 在模重寫正規形上透過線性脊反演、出現檢查（Occurs Check）、作用域逃逸阻斷與同元變數交集脊修剪（Spine Pruning）求得唯一最一般解。
3. **公理與定理 M11.T3（強制轉換菱形相干公理與函子升降合成定理）**：基底強制轉換圖通過 `verify_diamond_coherence` 保證任意平行路徑語義恆等；`synthesize_coercion` 沿乘積協變、函數逆變／協變（`(A1 -> B1) => (A2 -> B2)` 當 `A2 => A1` 且 `B1 => B2`）、結構紀錄寬度＋深度及受控遺忘去品牌化遞歸合成可執行強制轉換程式 `CoercionProg`。
4. **定理 M11.T4（64-bit Popcount 結構紀錄標準形與生成式名義品牌隔離定理）**：結構紀錄以 64-bit `field_mask` 排序儲存，達成宣告順序無關之唯一標準相等性與 $O(1)$ 欄位偏移定位 `popcount64(mask & ((1 << fid) - 1))`；生成式名義型別 `HNominal(id, name, S)` 對不同品牌 ID 嚴格禁止互轉（`id1 != id2 => None`），僅於顯式授權時提供遺忘伴隨態射 `Unbrand : Nominal(id, S) => S`。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 依賴多型宇宙代換與隱含元變數展開器 (`subst_poly_univs`, `instantiate_poly_scheme_implicits`) | `poly_implicit_unify_rewrite.mbt` | $O(k \cdot \|T\|)$ | 自動注入攜帶完整局部變數脊之語境元變數 |
| 終止性隱含重寫正規化器 (`verify_rewrite_rule_terminating`, `rewrite_normalize`) | `poly_implicit_unify_rewrite.mbt` | 多項式於項權重 | 靜態驗證 Knuth-Bendix 符號權重嚴格遞減與變數不倍增 |
| 模重寫 Miller 高階模式合一與脊修剪器 (`unify_modulo_rewrites`, `MetaStore::zonk`) | `poly_implicit_unify_rewrite.mbt` | 近線性於問題規模 | 實作線性脊反演、Occurs Check、Scope Escape 攔截與 Flex-Flex 脊交集修剪 |
| 硬體 SWAR 64-bit Popcount 與結構紀錄 $O(1)$ 投影 (`popcount64`, `mk_structural_record_ty/val`, `project_structural_field`) | `coercion_structural_nominal.mbt` | 投影嚴格常數時間 $O(1)$（12 條無分支位元算術） | 零雜湊碰撞、零線性搜尋之緊湊結構紀錄索引 |
| 菱形相干檢驗與函子強制轉換合成執行器 (`verify_diamond_coherence`, `synthesize_coercion`, `apply_coercion`) | `coercion_structural_nominal.mbt` | 寬度子型別快篩 $O(1)$：`(m_sup & ~m_sub) == 0` | BFS 最短典範基底路徑＋高階函數／結構紀錄／名義遺忘合成 |

---

## 三、資料夾視角的依賴關係圖

```text
                  [ 外部上游依賴：無（純獨立基礎模組） ]
                                    │
                                    ▼
             ┌─────────────────────────────────────────────┐
             │      dtt/m11_polymorphism_coercion_nom      │
             │       poly_implicit_unify_rewrite.mbt       │
             │       coercion_structural_nominal.mbt       │
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
1. `poly_implicit_unify_rewrite.mbt` 處理多型展開、隱含重寫與 Miller 高階模式合一，消解所有隱含參數元變數。
2. `coercion_structural_nominal.mbt` 建立結構紀錄與名義品牌混合類型系統，驗證強制轉換圖菱形相干並合成可執行轉換閉包。

### 輸出公共接口（Public API）
- **類型與錯誤**：`ElabTm`, `DepPolyScheme`, `MetaStore`, `ImplicitRewriteRule`, `HybridTy`, `HybridVal`, `CoercionProg`, `BaseCoercionEdge`, `CoercionEnv`, `PolyElabError`。
- **核心函式**：`subst_poly_univs`, `shift_elab`, `subst_elab`, `MetaStore::{new, fresh_meta, zonk}`, `instantiate_poly_scheme_implicits`, `relational_parametricity_arity`, `verify_rewrite_rule_terminating`, `rewrite_normalize`, `unify_modulo_rewrites`, `popcount64`, `mk_structural_record_ty`, `mk_structural_record_val`, `project_structural_field`, `seal_nominal`, `unseal_nominal`, `apply_coercion`, `CoercionEnv::{new, add_prim_coercion, allow_forgetful_unbrand, verify_diamond_coherence}`, `synthesize_coercion`。
