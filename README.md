# 姿态执行器保护脚本审计服务(octagon-auditor)

对姿态执行器保护脚本做**八边形抽象域**上的静态验证:上传前必须证明每次点火、
转向或增压指令(以包线断言建模)在所有可达程序点上都被不变量蕴含,绝不因有限
回放恰好未触发危险分支而放行。服务零第三方依赖,仅使用 Python 标准库。

## 输入模型

`POST /audit` 接收 JSON:

```json
{
  "num_registers": 2,                      // 1..4 个整数寄存器
  "initial": [{"lo": 0, "hi": 0},          // 每寄存器初始范围;lo/hi 可为 null(无界)
               {"lo": -5, "hi": 5}],
  "instructions": [ ... ]                  // 1..48 条,id 必须恰好为 0..N-1(稳定编号)
}
```

指令集(且仅含):

| op      | 字段                 | 语义                                   |
|---------|----------------------|----------------------------------------|
| `set`   | `reg`, `value`       | 常量赋值 `x_reg := value`              |
| `add`   | `reg`, `value`       | 常量增减 `x_reg := x_reg + value`      |
| `sub`   | `reg`, `value`       | 等价于 `add` 取负                      |
| `branch`| `cond`, `target`     | 比较分支,假方向顺序下落                |
| `goto`  | `target`             | 无条件跳转                             |
| `assert`| `cond`               | 包线断言(点火/转向/增压的允许包线)   |
| `halt`  | —                    | 终止;顺序走出末尾亦视为到达终止       |

条件为八边形片段:`{"coefs": {"0": 1, "1": -1}, "op": "<=", "value": 5}` 表示
`x0 - x1 <= 5`;`coefs` 至多两项、系数 ±1,比较符 ∈ `<= < >= > == !=`。
解析时统一规范化为 `<= / == / !=` 形态,响应中的条件文本均为规范化形式。

## 分析方法

- **八边形约束**:以差分界矩阵(DBM)维护各程序点 `±x_i ± x_j <= c` 形式的
  不变量,Floyd–Warshall 最短路 + 八边形整值 tightening 得到强闭包;
  `set`/`add`/分支收窄均为精确迁移(整数寄存器,减半步骤向下取整)。
- **回边闭包与 widening**:DFS 回边目标处施加固定规则 widening
  (凡变弱的分量放宽为 +∞),保证上升迭代终止。
- **widening 后持续复算**:自后不动点出发做下降迭代(Gauss–Seidel 取交),
  逐步回收 widening 损失的精度,每一步仍是后不动点。
- **终态校验**:输出前逐条转移显式复核 `f(inv[p]) ⊑ inv[q]`;响应中逐程序点
  给出规范化闭包约束与入边来源(`points.<id>.invariant` / `.incoming`),
  调用方可独立重放同一检查。

## 结论形态

- **`pass`**:每个可达断言均被该点不变量蕴含。附逐点不变量、入边来源、
  每条断言的逐项界核对(`assertions[].bounds`)与不动点元信息。
- **`fail`**:存在不可证断言。`first_unproven` 给出**首个按程序点编号**稳定
  裁决的位置、进入该点的抽象边界(`abstract_state`)及未被涵盖的包线条件
  (`uncovered`,含不变量实际能给出的界)。`kind: "abstract_alarm"` 明示这是
  抽象上近似告警,**并非具体执行反例**。不可达点上的断言记 `unreachable`,
  不阻塞放行。
- **`error`**:结构问题——寄存器越界、跳转悬空、不可解析约束、无可达终止等
  **合并反馈**于 `errors` 列表;响应不携带任何分析证据(无状态服务,每次请求
  独立计算,不存在旧证据)。

已知精度边界:`!=` 的真方向(`expr != k`)在单条边上按两个八边形析取支
(`expr <= k-1`、`-expr <= -k-1`)**各自独立收窄**:可达性与目标点断言核对
逐支进行,正负两个方向都不会被丢弃;仅当该析取信息在后续合流点被凸 join
合并后才可能失去关系(八边形是凸域,不表示一般析取)。`==` 的假方向不是
八边形约束,按恒等(不收窄)处理。两者均保持可靠,合流后可能产生抽象告警。

## 运行

```bash
# 本地
PORT=8080 python -m app.server
curl localhost:8080/health
curl -X POST localhost:8080/audit -d @script.json

# Compose(宿主机端口可配置,默认 8080)
AUDIT_HOST_PORT=9090 docker compose up --build app
```

接口:`GET /health`(健康路径)、`GET /`(服务信息)、`POST /audit`(审计接口)。
容器内端口由 `PORT` 配置,宿主机映射由 `AUDIT_HOST_PORT` 配置。

## 验证(verify 容器)

```bash
docker compose up --build --exit-code-from verify --abort-on-container-exit verify
```

`verify` 容器依次执行并以退出状态码报告结果(0 通过 / 1 失败):

1. **代码测试**:`python -m unittest discover -s tests -t .`(42 个用例,
   覆盖八边形域、分析器与 HTTP 接口;含转向保护脚本两类核心验收——
   危险正值必失败且程序点可达、安全非零放行且正负两向均保留);
2. **镜像构建检查**:`verify` 阶段 `FROM app` 阶段构建,构建 verify 即复核
   app 镜像可构建;冒烟时再将 `/health` 返回的版本与 `EXPECTED_VERSION` 比对,
   确认运行中的镜像即期望构建;
3. **HTTP 冒烟**(`scripts/smoke.py`):等待健康路径就绪后,核对放行用例
   (含循环关系不变量)、未证告警用例(首个未证点、抽象边界、未涵盖条件)、
   转向保护危险正值用例(失败、点可达、正值方向抽象边界)与安全非零用例
   (放行、点可达、正负两向不被丢弃)、结构错误合并反馈用例(四类错误齐备且
   无旧证据),并复测无状态性。

## 目录结构

```
app/octagon.py    八边形域:DBM、强闭包、迁移函数、格运算、规范化约束输出
app/program.py    指令解析、结构校验(合并反馈)、控制流图、widening 点
app/analyzer.py   上升/下降不动点引擎、终态校验、断言蕴含判定
app/server.py     HTTP 服务:GET /health,POST /audit
tests/            单元测试(unittest,零依赖)
scripts/smoke.py  verify 容器的 HTTP 冒烟
Dockerfile        多阶段:app(运行)/ verify(验证)
docker-compose.yml app 服务(可配置宿主机端口)+ verify 容器
```
