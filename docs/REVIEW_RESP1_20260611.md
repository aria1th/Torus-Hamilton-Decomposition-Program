아래는 **사람 증명으로 바로 승격 가능한 부분**과, 아직 살아 있는 leaf 병합 병목에 대한 **수학적 설계 인사이트**입니다. 업로드 번들 기준으로는 `D7(4)`, `D7(6)` root-flat certificate 검증은 재현되었고, G7 보조항은 README와 같이 **72/78 PASS, 6 FAIL**이 재현됩니다. 즉 개정본에는 “G7 실패를 숨기지 않고 endpoint-collision 보조정리로 교체”하는 방향이 맞습니다.

형식화 레포의 `growth_repair_gate_summary.json`, `growth_conjugate_search_summary.json` 자체는 이번 tar 안에는 없어서, A3·conjugate-search 수치는 브리핑의 전제를 사용했습니다. 다만 이번 번들 안의 `certificates/` 검증은 다음과 맞습니다: `D7(4)` root-flat size (4096), `D7(6)` root-flat size (46656), 둘 다 RF1/RF2/RF3 통과, 7개 return 모두 단일순환입니다.

---

## 1. Parity ledger 정리: 완전한 사람 증명

### 정리

root-flat layer schedule에서 색 (c), layer (t)의 layer map을 (U_{c,t}\in\mathrm{Sym}(X))라 하고

[
N_t=\prod_{c=0}^{d-1}\operatorname{sgn}(U_{c,t})
]

라 두자. 그러면 다음이 성립한다.

1. 같은 layer에서 두 색 사이의 RF2-legal read exchange는 (N_t)를 보존한다.
2. 모든 return
   [
   R_c=U_{c,m-1}\cdots U_{c,0}
   ]
   이 (K)-점 단일순환이고 (K)가 짝수이면
   [
   \prod_t N_t=(-1)^d.
   ]
3. 따라서 출발 schedule이 모든 layer에서 (N_t=+1)이고, 허용된 수선이 2색 read exchange뿐이라면, (d) 홀수에서 단일 return (d)개를 얻을 수 없다. 성공하려면 (N_t=-1)인 layer가 홀수 개 필요하고, 그런 layer는 2색 exchange로 만들 수 없으므로 최소한 하나의 **3색 이상 wild seam**이 필요하다.

### 핵심 보조정리: 2색 exchange의 부호 보존

(X)를 유한 집합, (f,g\in\mathrm{Sym}(X))를 같은 layer의 두 색 layer map이라 하자. 어떤 부분집합 (A\subset X)에서 두 색의 이미지를 맞바꾸어

[
f_A(x)=
\begin{cases}
g(x),&x\in A,\
f(x),&x\notin A,
\end{cases}
\qquad
g_A(x)=
\begin{cases}
f(x),&x\in A,\
g(x),&x\notin A
\end{cases}
]

라 하자. 이 exchange가 RF2-legal, 즉 (f_A,g_A)가 모두 전단사라고 하자. 그러면

[
\operatorname{sgn}(f_A)\operatorname{sgn}(g_A)
==============================================

\operatorname{sgn}(f)\operatorname{sgn}(g).
]

**증명.** (h=f^{-1}g)라 두면

[
f_A(X)=f(X\setminus A)\cup g(A)
=f\big((X\setminus A)\cup h(A)\big).
]

따라서 (f_A)가 전단사이려면 (h(A)=A)여야 한다. 즉 (A)는 (h)-순환들의 합집합이다. 이때

[
\psi_A(x)=
\begin{cases}
h(x),&x\in A,\
x,&x\notin A
\end{cases}
]

라 두면

[
f_A=f\circ\psi_A,\qquad
g_A=g\circ\psi_A^{-1}.
]

따라서

[
\operatorname{sgn}(f_A)\operatorname{sgn}(g_A)
==============================================

\operatorname{sgn}(f)\operatorname{sgn}(g)
\operatorname{sgn}(\psi_A)\operatorname{sgn}(\psi_A^{-1})
=========================================================

\operatorname{sgn}(f)\operatorname{sgn}(g).
]

다른 색은 변하지 않으므로 layer product (N_t)도 보존된다. ∎

### ledger 등식의 증명

부호는 합성에 대해 곱셈적이므로

[
\operatorname{sgn}(R_c)
=======================

\prod_t \operatorname{sgn}(U_{c,t}).
]

색 (c)에 대해 다시 곱하면

[
\prod_c \operatorname{sgn}(R_c)
===============================

# \prod_c\prod_t\operatorname{sgn}(U_{c,t})

# \prod_t\prod_c\operatorname{sgn}(U_{c,t})

\prod_t N_t.
]

한편 (K)-cycle의 부호는 ((-1)^{K-1})이다. (K)가 짝수이면 각 단일 return은 홀치환이다. 따라서

[
\prod_c \operatorname{sgn}(R_c)=(-1)^d.
]

즉

[
\prod_tN_t=(-1)^d.
]

이것이 parity ledger다. ∎

### 논문용 해석

이 정리는 “2색 exchange는 gauge move이고, parity를 바꾸지 못한다”는 말로 요약됩니다. (d=9)에서는 단일순환 9개가 전체 ledger에 (-1)을 요구합니다. 출발 growthDir가 layer별 (N_t=+1)이면, 아무리 2색 exchange를 쌓아도 ledger는 (+1)에 갇힙니다. 그러므로 leaf 병합 수선에는 **홀수 개의 parity-changing wild layer**가 필수입니다.

특히 (K_2=m^8)은 짝수이므로 leaf return 하나가 단일순환이려면 그 return 자체가 홀치환이어야 합니다. 기계가 확인한 것처럼 growthDir의 (\nu_0) return이 짝치환으로 고정되어 있다면, cycle enumeration 없이도 (\nu_0)는 단일순환이 될 수 없습니다. 이것이 A3의 가장 깨끗한 국소 부호 장애입니다.

---

## 2. Budget 포화 정리: chained 보존형 성장의 사망진단서

여기서는 더 강한 사실이 나옵니다. parity는 “부호” 장애이고, budget은 “read 총량” 장애입니다. 두 번째는 보존형 chained growth를 (d,m) 일양으로 죽입니다.

### L1. Count-vector 유일성

한 색의 first-return 궤적은 정확히 (m)개의 layer step으로 이루어진다. 어떤 old (x)-방향 (i)를 읽은 횟수를 (n_i(p))라 하자. 그러면

[
n_i(p)\equiv (R(p)-p)_i \pmod m,
\qquad
\sum_i n_i(p)\le m.
]

또 (R(p)\ne p)이면 (n_i(p))는 잔차

[
r_i(p):=((R(p)-p)_i\bmod m)\in{0,\ldots,m-1}
]

로 유일하게 결정된다.

**증명.** (n_i\equiv a_i\pmod m), (0\le n_i\le m)이다. (a_i\ne0)이면 (n_i=a_i)밖에 없다. (a_i=0)이면 (n_i=0) 또는 (m)일 수 있다. 그런데 어떤 (n_i=m)이 발생하면 (\sum_j n_j\le m) 때문에 모든 다른 (n_j)는 0이어야 하고, 따라서 전체 displacement가 0이다. 이는 (R(p)=p)를 뜻한다. fixed point가 없으면 불가능하다. 따라서 모든 (n_i)는 least residue (r_i(p))와 같다. ∎

이 증명은 사실 (m=4,6) 전수조사보다 더 강합니다. 전수조사는 certificate 확인용이고, 사람 증명은 위 잔차 논리로 충분합니다.

### L2. Read 총량은 return만의 함수

RF2, 즉 각 layer map의 전단사성을 가정하자. 색 (c)가 방향 (i)를 읽은 총량은

[
\sum_{p\in X} r_i^{(c)}(p)
]

이다. 특히 이 값은 layer 내부의 구현이 아니라 return (R_c)만으로 결정된다.

**증명.** (p)에서 출발한 색 (c) 궤적의 (t)-번째 layer 진입점을

[
p_t=U_{c,t-1}\cdots U_{c,0}(p)
]

라 하자. RF2 때문에 각 prefix map은 전단사이다. 따라서 (p)가 (X) 전체를 돌면 (p_t)도 (X) 전체를 정확히 한 번 돈다. 그러므로 모든 출발점의 궤적에서 방향 (i)가 읽힌 횟수의 합은 실제 layer table 전체에서 색 (c)가 방향 (i)를 읽은 row 수와 같다. L1에 의해 각 궤적의 해당 횟수는 (r_i^{(c)}(p))이다. ∎

### L3. Latin schedule의 방향별 포화

(X)의 크기를 (K)라 하자. RF1 Latin 조건은 각 layer (t), 각 row (x)에서 색들이 방향들을 정확히 한 번씩 사용한다고 말한다. 따라서 고정된 old (x)-방향 (i)에 대해 전체 read slot 수는

[
mK
]

이다. L2와 합치면

[
D_i
===

# \sum_c\sum_{x\in X} ((R_cx-x)_i\bmod m)

mK.
]

업로드 certificate에서 실제로

[
m=4:\quad 16384=4\cdot4096,
]
[
m=6:\quad 279936=6\cdot46656
]

가 재현됩니다.

### Kill theorem

old base section을 (X), (|X|=K)라 하고, (+2) 성장 후 child section을

[
X\times Z,\qquad Z=(\mathbb Z/m\mathbb Z)^2
]

로 쓰자. 따라서

[
K_2=|X||Z|=m^2K.
]

old color들의 child return이 old (x)-return을 pointwise 보존한다고 하자. 즉 old color (c)의 child return의 (x)-성분은

[
(x,z)\mapsto R_c(x)
]

이다. 그러면 old color (c)의 방향 (i) read 총량은

[
\sum_{(x,z)\in X\times Z} r_i^{(c)}(x)
======================================

m^2\sum_{x\in X}r_i^{(c)}(x).
]

old color 전체에 대해 합하면 L3에 의해

[
\sum_{\text{old }c}\operatorname{Read}_{c,i}^{+}
================================================

# m^2\cdot mK

mK_2.
]

그런데 child Latin 조건에서 방향 (i)의 전체 read slot 역시 정확히 (mK_2)개다. 따라서 old colors가 방향 (i)의 모든 slot을 이미 소진한다. 모든 old (x)-방향 (i)에 대해 동일하므로 leaf 색들은 (x)-방향을 한 번도 읽을 수 없다.

따라서 leaf return은 각 fiber

[
{x}\times Z
]

를 보존한다. 각 fiber의 크기는 (m^2)이고, fiber 수는

[
|X|=K=K_2/m^2.
]

그러므로 leaf return은 적어도 (K_2/m^2)개의 cycle을 가진다. (7\to9)에서는 (K=m^6)이므로 leaf return은 적어도

[
m^6
]

개의 cycle을 가진다. 단일 (m^8)-cycle은 불가능하다. ∎

### 논문용 해석

이 정리는 chained 보존형 growth를 탐색 실패가 아니라 **정리로 폐기**합니다.

핵심 문장은 다음입니다.

> Old return을 pointwise 보존하면 old 색들의 read shadow가 child에서 (m^2)배 복제되고, 그 복제량이 모든 (x)-direction slot을 정확히 포화한다. Leaf는 (x)-방향을 굶으므로 (x)-fiber들을 병합할 수 없다.

따라서 pass38의 ordinary 고짝수 단계는 이 정리에 걸리지 않습니다. ordinary 단계는 old return을 pointwise lift하지 않고 row를 새로 실현하므로, old read shadow가 그대로 (m^2)배 복제된다는 가정이 깨집니다. 죽는 것은 정확히 “보존형 chained growth”입니다.

---

## 3. G7 midpoint 실패의 올바른 replacement: endpoint-collision lemma

현재 `def:growth-midpoint-translate`류의 boundary-avoidance 문장은 “bad endpoint label을 피하면 old projection이 0”이라는 형태인데, certificate는 이 일반형이 틀렸음을 정확히 보여줍니다. 문제는 badness가 endpoint label이 아니라 **endpoint pair의 midpoint center**에 산다는 점입니다.

### 정확한 일반형

row (r)의 four-point window를 (W_r), quotient cut을

[
\vartheta:W_r\to \mathbb Z
]

라 하자. old incidence line (u_i-u_j)를 center (\lambda)로 translate하면 endpoints는

[
i_\lambda=\lambda+\frac{i-j}{2},
\qquad
j_\lambda=\lambda-\frac{i-j}{2}.
]

이 line이 nonzero projection을 만들려면 반드시

[
i_\lambda,j_\lambda\in W_r,
\qquad
\vartheta(i_\lambda)\ne\vartheta(j_\lambda)
]

이어야 한다. 이때

[
\lambda=\frac{i_\lambda+j_\lambda}{2}.
]

따라서 피해야 할 집합은 endpoint label set이 아니라

[
C_r
===

\left{
\frac{a+b}{2}:
a,b\in W_r,\
\vartheta(a)\ne\vartheta(b),
u_a-u_b\text{가 어떤 old generator translate와 충돌}
\right}.
]

정확한 lemma는 다음입니다.

> If (G_{r,\rho}\cap C_r=\varnothing), then every translated old generator visible through the guide centers has zero image in (P/L).

증명은 한 줄입니다. Nonzero image가 있다면 endpoints (a,b)가 cut의 양쪽에 있고, 그 midpoint ((a+b)/2)가 guide center에 속한다. 이는 (G_{r,\rho}\cap C_r\ne\varnothing)이다. 대우를 취하면 됩니다.

### certificate 실패와의 일치

chained row 1:

* window: ({0,2,7,5})
* old endpoint nonzero pairs: ((7,2)), ((7,5))
* bad centers:
  [
  (7+2)/2=0,\qquad (7+5)/2=6.
  ]
* literal reading에서는 new label (0)도 window endpoint로 허용되어 ((0,7))이 추가되고,
  [
  (0+7)/2=8
  ]
  이 bad center가 된다.
* 기록 phase (\rho=1), (\delta=2)는
  [
  G_{r,\rho}={8,1,3}
  ]
  이므로 old-endpoint reading은 통과하지만 literal reading은 center (8) 때문에 실패한다.

chained row 2:

* 핵심 old nonzero pair는 ((2,8))
* bad center:
  [
  (2+8)/2=5.
  ]
* boundary-avoiding phase (\rho\in{4,5,6})의 guide center들은 각각
  [
  {3,4,5},\quad {4,5,6},\quad {5,6,7}
  ]
  이라서 모두 center (5)를 포함한다.
* 따라서 old-endpoint reading에서도 discharge phase가 없다.

즉 6개의 FAIL은 우연한 저차원 사고가 아니라, midpoint-translate lemma의 일반형이 “endpoint avoidance”가 아니라 “midpoint collision avoidance”여야 함을 보여주는 certificate입니다.

논문에서는 `B_r`를 endpoint boundary set으로 두는 대신, row별 bad-center set (C_r)를 정의하는 것이 안전합니다. 더 강하지만 간단한 sufficient condition은

[
G_{r,\rho}\cap
\left{\frac{a+b}{2}:a,b\in W_r,\ a\ne b\right}
=\varnothing
]

입니다. 단, 이 강한 조건은 phase 존재성이 약해질 수 있으므로 실제로는 cut-separated pair만 넣은 (C_r)가 맞습니다.

---

## 4. Leaf 병합 설계: 무엇을 만들어야 하는가

Budget theorem 때문에 pointwise 보존형은 죽었습니다. conjugate 완화에서 살아남으려면 old color가 leaf에게 (x)-read를 **양도**해야 합니다. 이때 중요한 것은 “양도량”만이 아니라, RF2가 강제하는 양도 단위입니다.

### 4.1 Ribbon lemma: RF2가 강제하는 최소 단위

한 layer에서 donor old map을 (D), leaf map을 (L)이라 하자. 어떤 support (A)에서 donor와 leaf의 read를 교환한다고 하자. 위 2색 exchange 보조정리와 같은 논리로, 교환 후에도 두 map이 전단사이려면

[
A
]

는

[
h=L^{-1}D
]

의 순환들의 합집합이어야 한다.

즉 RF2-legal donation은 임의의 점집합에서 일어날 수 없고, (L^{-1}D)-orbit을 따라 닫혀야 합니다. product 좌표로 보면 이 orbit이 바로 staircase입니다. donor가 (x)-step을 leaf에게 주면, donor는 leaf의 gated (z)-step을 인수하고, 다음 가능한 교환 위치는 (L^{-1}D)가 지정합니다. 이것이 “ribbon이 RF2를 닫는 최소 양도 단위”라는 말의 사람 증명입니다.

### 4.2 Leaf당 최소 (m^6) x-read

leaf return이 어떤 (x)-fiber

[
{x}\times Z
]

에서 한 번도 (x)-read를 하지 않으면 그 fiber는 leaf return 아래 invariant입니다. 단일순환이 되려면 모든 (x)-fiber에서 적어도 한 번은 탈출해야 합니다. (7\to9)에서 (x)-fiber 수는 (m^6)이므로 leaf 하나당 최소 (m^6)개의 (x)-read donation이 필요합니다. 두 leaf에는 합계 최소

[
2m^6
]

이 필요합니다. 수치로는

[
m=4:\ 2m^6=8192,\qquad
m=6:\ 2m^6=93312.
]

이 하한은 단순 counting이지만, 실제로는 RF2 때문에 이 read들이 ribbon 단위로 묶여야 하므로 더 강한 구조 제약을 냅니다.

### 4.3 Donated-orbit graph

각 leaf (\nu)에 대해 graph (G_\nu)를 다음처럼 둡니다.

* vertex: old fiber (x\in X)
* edge: leaf 궤적이 donation을 통해 (x)-fiber에서 (x')-fiber로 이동하는 사건

그러면 leaf cycle은 (G_\nu)의 connected component 밖으로 나갈 수 없습니다. 따라서 leaf return이 단일순환이려면 (G_\nu)는 spanning connected이어야 합니다. 방향까지 고려하면 base quotient가 하나의 directed orbit을 가져야 합니다.

하지만 connectedness만으로는 충분하지 않습니다. (G_\nu) 위에서 (z)-fiber의 holonomy가 남습니다. Skew-product 관점에서 leaf return은 대략

[
(x,z)\mapsto (T x, A_x z)
]

꼴이고, base (T)가 하나의 cycle이더라도 전체가 하나의 cycle이 되려면 base 한 바퀴의 holonomy

[
A_{T^{K-1}x}\cdots A_{Tx}A_x
]

가 (Z=(\mathbb Z/m)^2) 위에서 (m^2)-cycle이어야 합니다.

여기서 중요한 함정이 있습니다. (Z)-plane에서 순수 translation은 order가 최대 (m)입니다. 따라서 pure rotor나 product translation만으로는 (m^2)-cycle holonomy를 만들 수 없습니다. (m^2)-cycle을 만들려면 lexicographic carry, snake, rail-seam류의 **비선형 또는 piecewise carry**가 필요합니다. 이것이 “wild ((z_0,z_1))-layer”가 단순 장식이 아니라 구조적으로 필요한 이유입니다.

### 4.4 왜 annealer가 old/parity는 맞추고 leaf에서 멈추는가

브리핑의 최고 후보가 old 색 단일성과 parity를 상당히 잘 맞추면서도 leaf cycle floor (15,7)에서 막힌다는 것은 자연스럽습니다.

* old colors: conjugate 완화에서는 old return이 pointwise 고정되지 않으므로 cyclicity를 회복할 자유도가 큽니다.
* parity: wild seam 하나와 correction line으로 ledger는 비교적 쉽게 맞출 수 있습니다.
* leaf: 남은 문제는 donated graph의 connectedness와 (z)-holonomy transitivity입니다. 이 둘은 훨씬 더 강합니다.

작은 홀수 cycle floor가 반복된다면, 그것은 parity가 아니라 holonomy orbit index일 가능성이 큽니다. 즉 leaf return이 어떤 숨은 block system 또는 congruence class를 보존하고 있을 수 있습니다. 이때 correction line은 단순히 (\nu_0)의 부호를 뒤집는 역할을 넘어서, 그 block system을 깨야 합니다.

구체적으로 다음 invariant를 검사하면 좋습니다.

1. donated graph (G_\nu)의 component 수와 directed quotient cycle 수;
2. spanning tree를 고른 뒤 fundamental cycle마다 생기는 (z)-holonomy subgroup;
3. leaf cycle decomposition이 어떤 함수
   [
   \chi(x,z)\in A
   ]
   를 보존하는지;
4. correction (z_1)-line이 (\chi)를 실제로 바꾸는지;
5. base 한 바퀴 holonomy가 (Z)-plane에서 (m^2)-cycle인지, 아니면 (7), (15), (35) 같은 orbit index를 남기는지.

이 관점에서 목표물은 다음처럼 정식화됩니다.

> Find RF2-closed donation ribbons whose projection graph on (X) is spanning connected, and whose induced (z)-holonomy over one base circuit is an (m^2)-cycle. Add an odd number of parity-changing 3-color wild seams so that the parity ledger is also correct, while old colors remain cyclic.

---

## 5. 개정 논문의 서사 구조 제안

개정본에서는 chained 단계 폐기를 다음 세 문장으로 정리하면 가장 설득력이 큽니다.

1. **Parity ledger:** 2색 exchange는 layer sign product를 보존한다. (d=9) 단일 return들은 ledger (-1)을 요구하므로, parity-changing wild seam이 필수다.
2. **Read budget:** old return을 pointwise 보존하면 old colors가 child의 모든 (x)-read slot을 포화한다. leaf는 (x)-fiber를 벗어날 수 없어 적어도 (m^6)개의 cycle을 가진다.
3. **Therefore:** chained preservation growth는 탐색 실패가 아니라 구조적으로 불가능하다. 살아 있는 경로는 pointwise 보존을 버리는 conjugate repair이며, 그 핵심은 RF2-closed donation ribbon과 (z)-plane wild holonomy다.

이렇게 쓰면 A3의 세 장애가 서로 흩어진 check가 아니라 하나의 그림으로 묶입니다.

* alphabet confinement: leaf가 충분한 (x)-read를 얻지 못하면 fiber/block에 갇힌다.
* skeleton 부재: wild 기반에서는 old transport를 pointwise로 밀 수 없다.
* z-independent child: (z)-holonomy가 primitive하지 않으면 최소 (m)개 이상의 cycle이 남는다.
* parity obstruction: 2색 repair만으로는 ledger를 바꿀 수 없다.

---

## 6. endpoint/ordinary interface에 대한 소품 정리

G7의 6개 FAIL은 package에 그대로 싣는 편이 맞습니다. 다만 본문 lemma는 다음 형태로 바꾸는 것이 좋습니다.

기존 문장:

> (G_{r,\rho}\cap B_r=\varnothing)이면 old projection이 0이다.

교체 문장:

> (G_{r,\rho})가 cut-separated endpoint pairs의 midpoint collision set (C_r)을 피하면 old projection이 0이다.

그리고 proof는:

[
\Theta(u_i-u_j)\ne0
\Rightarrow
i_\lambda,j_\lambda\in W_r,\ \vartheta(i_\lambda)\ne\vartheta(j_\lambda)
\Rightarrow
\lambda=\frac{i_\lambda+j_\lambda}{2}\in C_r.
]

이 형태는 Lean/GuideLocality류의 endpoint-collision 형식과도 정합합니다. 특히 center가 모든 가능한 endpoint collision midpoint를 피하면 discharge는 자명합니다. 반대로 이번 G7 실패는 center (5), (8), (4)가 정확히 nonzero endpoint pair의 midpoint였기 때문에 발생합니다.

---

## 결론

지금 사람 증명으로 확정 가능한 핵심은 두 개입니다.

[
\boxed{\text{2색 exchange는 parity ledger를 바꾸지 못한다.}}
]

[
\boxed{\text{old return pointwise 보존은 모든 leaf }x\text{-read를 굶긴다.}}
]

첫 번째는 “왜 wild seam이 필요한가”를 설명하고, 두 번째는 “왜 chained 보존형 growth가 죽었는가”를 설명합니다. 남은 conjugate repair의 본질은 더 이상 old return을 보존하는 것이 아니라, old colors의 cyclicity를 유지하면서 leaf에게 RF2-closed ribbon 단위로 (x)-read를 기부하고, 그 기부 graph의 (z)-holonomy를 (m^2)-cycle로 만드는 것입니다.
## 판정 요약

현재 전체 증명은 **무조건적으로 닫힌 상태가 아닙니다.** 더 정확히는:

[
\boxed{\text{기존 원고의 chained }7\to9\text{ 성장 명제는 현재 형태로 폐기되어야 합니다.}}
]

그리고 전체 정리는 지금

[
\boxed{
\text{“conjugate repair 또는 대체 odd-low 전파가 존재한다”는 조건부 상태}
}
]

입니다.

다만 이것은 “모든 것이 미결”이라는 뜻은 아닙니다. 오히려 감사 결과는 상당히 선명합니다.

1. **기반 certificate 자체는 살아 있습니다.**
   `D7(4)`, `D7(6)` pointwise root-flat certificate는 RF1/RF2/RF3와 7개 return 단일순환을 통과합니다. 즉 (\RHD(7,4)), (\RHD(7,6)) 수준의 pointwise 기반은 유효합니다.

2. **그 기반을 chained growth 입력 (\HED(7,m))으로 쓰는 증명은 닫히지 않습니다.**
   `check_hed_clauses.py`를 재실행하면 `72/78 PASS, 6 FAIL`입니다. 실패는 모두 G7e/G7f discharge 실패이고, 정확히 chained (7\to9) 인터페이스의 old-generator projection 방전 실패입니다.

3. **old return pointwise 보존형 (+2) 성장은 구조적으로 불가능합니다.**
   budget 포화 정리가 이를 사람 증명으로 죽입니다. 그러므로 기존 chained growth를 “조금 고쳐서 같은 타입으로 살리는” 방향은 안 됩니다.

4. **남은 병목은 leaf 병합입니다.**
   old colors를 단일순환으로 유지하면서 두 leaf (\nu_0,\nu_1)를 각각 (m^8)-단일순환으로 만드는 **non-pointwise conjugate repair**가 필요합니다.

---

# 1. 전체 정리의 현재 논리 상태

원고의 최종 유도는 대략 다음 의존성을 가집니다.

[
\HD(d,m)
\Leftarrow
\begin{cases}
d\text{ even}: \text{phase doubling from } \HD(d/2,m),\
d\text{ odd high-even}: \HED(7,m)\to \HED(9,m)\to \cdots,\
d\text{ odd low-modulus}: \HED(7,4/6)\to \HED(9,4/6)\to \cdots.
\end{cases}
]

문제는 모든 odd branch가 결국 다음 관문을 통과한다는 점입니다.

[
\boxed{\HED(7,m)\longrightarrow \HED(9,m)}
]

현재 원고의 `prop:chained-two-hole`가 바로 이 관문입니다. 그런데 이 관문이 두 이유로 닫히지 않습니다.

첫째, certificate 수준에서 boundary-avoiding phase가 old projection을 죽인다는 주장이 실패합니다. 구체적으로 `D7(4)`, `D7(6)` 모두에서 chained row 1의 literal discharge, chained row 2의 old-endpoint discharge와 literal discharge가 실패합니다.

둘째, 더 강하게는 budget 포화 정리가 old return pointwise 보존형 (+2) growth 전체를 불가능하게 만듭니다. 따라서 실패는 단순한 phase 선택 실수가 아니라, 기존 chained 방식의 구조적 사망입니다.

결론:

[
\boxed{
\text{현재 원고의 “모든 even modulus, 모든 }d\text{” 정리는 조건부입니다.}
}
]

조건은 다음 중 하나입니다.

[
\boxed{
\text{conjugate }7\to9\text{ repair를 구성한다}
}
]

또는

[
\boxed{
\text{odd-low / odd-high 전파를 chained 없이 새로 구성한다.}
}
]

---

# 2. 무엇이 무조건 확정인가

## 2.1 Parity ledger 정리

이 부분은 **무조건적인 수학 정리**입니다.

층상 schedule에서 layer (t)의 색별 layer map 부호 곱을

[
N_t=\prod_c \operatorname{sgn}(U_{c,t})
]

라 하면,

[
\prod_t N_t
===========

\prod_c \operatorname{sgn}(R_c).
]

각 return (R_c)가 짝수 크기 (K)의 단일순환이면

[
\operatorname{sgn}(R_c)=(-1)^{K-1}=-1.
]

따라서 (d)개 return이 모두 단일순환이면

[
\prod_t N_t=(-1)^d.
]

또 RF2-legal 2색 exchange는 같은 layer의 두 치환 (f,g)를 (f\psi,\ g\psi^{-1}) 형태로 바꾸므로

[
\operatorname{sgn}(f)\operatorname{sgn}(g)
]

를 보존합니다. 즉 2색 exchange는 (N_t)를 바꾸지 못합니다.

따라서 (d=9)에서 모든 return을 단일순환으로 만들려면 전체 ledger가 (-1)이어야 하고, 출발 growthDir가 layerwise even이면 2색 exchange만으로는 도달 불가능합니다.

이것은 완성 정리로 써도 됩니다.

---

## 2.2 Budget 포화 정리

이 부분도 **무조건적인 수학 정리**입니다. 가정은 명확합니다.

* root-flat / RF2 layer bijection,
* old return pointwise 보존,
* Latin read budget,
* old return들이 fixed-point-free, 실제로는 단일순환.

그러면 old colors의 return displacement가 read 총량을 결정합니다.

고정된 방향 (i)에 대해 한 궤적의 read count (n_i(p))는

[
n_i(p)\equiv (R(p)-p)_i \pmod m,
\qquad
\sum_i n_i(p)\le m
]

를 만족합니다. fixed point가 없으면 (n_i(p))는 least residue

[
r_i(p)=((R(p)-p)_i\bmod m)
]

로 유일합니다.

RF2 때문에 prefix layer maps가 전단사이므로, 색 (c)의 방향 (i) read 총량은

[
\sum_p r_i^{(c)}(p)
]

입니다. 즉 return만의 함수입니다.

이제 (+2) child에서 old return을 pointwise 보존하면 old read shadow가 (m^2)배 복제됩니다. 기반에서 방향 (i)의 총 read budget이 (mK)이고 child section 크기가 (K_2=m^2K)이므로 old colors만으로

[
m^2\cdot mK=mK_2
]

를 소모합니다. 이것은 child의 방향 (i) 전체 슬롯과 정확히 같습니다.

따라서 leaf colors의 (x)-read budget은 0입니다. leaf return은 각 fiber

[
{x}\times(\mathbb Z/m)^2
]

를 보존하므로 적어도

[
K_2/m^2=m^6
]

개의 cycle을 가집니다. 단일 (m^8)-cycle은 불가능합니다.

즉 다음은 확정입니다.

[
\boxed{
\text{old return pointwise 보존형 chained }d\to d+2\text{ growth는 불가능}
}
]

이것은 탐색 실패가 아니라 정리입니다.

---

## 2.3 `D7(4)`, `D7(6)` pointwise 기반

업로드 번들의 certificate 기준으로 다음은 확정입니다.

* `D7_4`: root-flat size (4096=4^6), RF1/RF2/RF3 통과, 7개 return cycle lengths 모두 `[4096]`.
* `D7_6`: root-flat size (46656=6^6), RF1/RF2/RF3 통과, 7개 return cycle lengths 모두 `[46656]`.
* marked witness, singleton common edge, reserve separation도 통과.

따라서 (\RHD(7,4)), (\RHD(7,6)) 수준의 기반은 살아 있습니다.

하지만 이것은 곧바로 “usable (\HED(7,4)), (\HED(7,6))”를 뜻하지 않습니다. (\HED)가 다음 growth를 실제로 가능하게 하려면 old-generator discharge가 필요하고, 바로 그 G7e/G7f가 실패합니다.

---

# 3. 무엇이 조건부인가

## 3.1 전체 theorem

현재 전체 theorem

[
\forall d\ge2,\ \forall \text{ even }m\ge4,\quad \HD(d,m)
]

은 조건부입니다.

조건은 다음 중 하나입니다.

### 조건 A: conjugate (7\to9) repair

old return을 pointwise 보존하지 않고, 대신 old colors의 child return이 단일 (m^8)-cycle이 되도록 conjugate 완화하는 수선이 필요합니다.

즉 기존의

[
R_c^{child}(x,z)=(R_c^{old}(x),z)
]

꼴은 불가능하고, 다음 정도의 자유가 필요합니다.

[
R_c^{child}(x,z)
================

(\widetilde R_c(x,z),\widetilde z_c(x,z)),
]

단 old colors도 단일순환, leaf colors도 단일순환이어야 합니다.

### 조건 B: 직접 (D9) family

chained (7\to9)를 버리고, 모든 even (m\ge4)에 대해 직접적인 (\HED(9,m)) 또는 적어도 이후 paired growth에 넣을 수 있는 (\RHD/\HED(9,m)) family를 구성해도 됩니다.

단순히 (m=4,6)의 finite (D9) certificate만으로는 전체 정리가 닫히지 않습니다. high-even (m>9) 및 (m=8) 등도 처리해야 하기 때문입니다.

### 조건 C: odd-low 전파 재설계

rail-seam 문법을 고차원화해서 홀수 차원 branch 자체를 새로 만들 수 있습니다. 이 경우 chained (7\to9)는 필요 없어질 수 있습니다.

---

## 3.2 현재 conjugate repair 탐색 결과

브리핑의 탐색 상태는 **증거**이지 증명은 아닙니다.

* old 색 단일성 회복: 가능해 보임.
* parity ledger: wild seam으로 맞출 수 있음.
* leaf 병합: 아직 실패.
* 최고 후보 cycle type:
  [
  [1,3,5,3,5,1,5,35,23]
  ]
* leaf floor:
  [
  \nu_0=15,\qquad \nu_1=7.
  ]

이 상태는 “family 내 장애가 아직 없다”를 뜻하지, “수선이 존재한다”를 뜻하지 않습니다. 작은 홀수 cycle floor가 안정적으로 남으면 family-specific congruence invariant가 있을 가능성도 있습니다.

따라서 conjugate repair는 현재 명백히 조건부입니다.

---

# 4. 무엇이 반증되었거나 폐기되어야 하는가

## 4.1 기존 `prop:chained-two-hole`

현재 원고의 명제:

[
\HED(7,m)\Rightarrow \HED(9,m)
]

을 기존 chained two-hole construction으로 증명하는 부분은 현재 형태로는 사용할 수 없습니다.

두 가지 독립 이유가 있습니다.

### 이유 1: projection discharge 실패

`check_hed_clauses.py`에서 다음이 실패합니다.

* chained row 1: G7f literal discharge 실패.
* chained row 2: G7e old-endpoint discharge 실패.
* chained row 2: G7f literal discharge 실패.

각각 (m=4), (m=6)에서 동일하게 발생하여 총 6개 실패입니다.

특히 chained row 2에서는 boundary-avoiding phase들이 모두 center (5)를 포함하고, center (5)가 nonzero pair ((2,8))의 midpoint입니다. 따라서

[
G_{r,\rho}\cap B_r=\varnothing
]

이어도 old projection이 0이 되지 않습니다.

즉 원고의 핵심 implication

[
G_{r,\rho}\cap B_r=\varnothing
\Longrightarrow
\Theta(H^-_r)=0
]

이 거짓입니다.

### 이유 2: budget theorem

설령 projection lemma를 국소적으로 고쳐도, old return을 pointwise 보존하는 chained growth는 budget 포화 때문에 불가능합니다.

따라서 기존 chained route는 단순 수정 대상이 아니라 폐기 대상입니다.

---

## 4.2 `growth-midpoint-translate`의 endpoint-boundary formulation

기존 형식:

[
G_{r,\rho}\cap B_r=\varnothing
]

에서 (B_r)를 endpoint boundary set으로 두는 방식은 틀렸습니다.

정확한 장애는 endpoint가 아니라 midpoint입니다. Nonzero projection은 cut-separated endpoint pair ((a,b))가 생길 때 발생하고, 그 translate center는

[
\lambda=\frac{a+b}{2}
]

입니다. 따라서 피해야 하는 것은

[
C_r=
\left{
\frac{a+b}{2}:
a,b\in W_r,\
\vartheta(a)\ne\vartheta(b)
\right}
]

류의 midpoint collision set입니다.

즉 교체해야 할 lemma는 다음 형태입니다.

[
G_{r,\rho}\cap C_r=\varnothing
\Longrightarrow
\Theta(H^-_r)=0.
]

이 수선은 ordinary interface의 서술에는 필요합니다. 하지만 이것만으로 chained (7\to9)가 살아나지는 않습니다.

---

# 5. 현재 증명으로 닫히는 범위

전체 theorem은 닫히지 않았지만, 유도 구조상 일부 범위는 여전히 닫힙니다. (d)에서 2의 거듭제곱 인자를 제거한 odd core를

[
d_{\mathrm{odd}}=\frac d{2^{v_2(d)}}
]

라 하겠습니다.

현재 구성 요소들을 받아들이면, 대략 다음 범위는 닫힙니다.

[
d_{\mathrm{odd}}\in{1,3,5,7}.
]

여기서 (d_{\mathrm{odd}}=1)은 반복 phase-doubling으로 (d=2) base까지 내려가는 경우입니다.

* (d_{\mathrm{odd}}=3): (D3) base와 phase doubling.
* (d_{\mathrm{odd}}=5): (D5) high-even anchor 및 (D5(4)) reset.
* (d_{\mathrm{odd}}=7): (D7(4),D7(6)) pointwise bases와 (D7) high-even anchor.

하지만

[
\boxed{
d_{\mathrm{odd}}\ge9
}
]

인 경우는 현재 proof route가 반드시 odd (+2) propagation, 특히 (7\to9) 또는 그 대체물을 요구합니다. 이 부분이 미결입니다.

따라서 전체 theorem의 미해결 core는 사실상 다음 하나로 압축됩니다.

[
\boxed{
\text{odd dimension }9\text{ 이상을 여는 첫 성장 단계}
}
]

---

# 6. 진짜 병목: leaf 병합

현재 병목은 G7 bookkeeping 자체가 아닙니다. G7 실패는 증상입니다. 본질은 leaf 병합입니다.

Budget theorem에 의해 leaf colors가 단일순환이 되려면 각 leaf는 최소한

[
m^6
]

개의 (x)-fiber를 탈출해야 합니다. 두 leaf 전체로는 최소

[
2m^6
]

개의 (x)-read donation이 필요합니다.

수치상:

[
m=4:\quad 2m^6=8192,
]
[
m=6:\quad 2m^6=93312.
]

그런데 RF2 때문에 donation은 임의의 점집합에서 할 수 없습니다. donor map (D), leaf map (L) 사이에서 2색 exchange를 하려면 support (A)가

[
L^{-1}D
]

의 orbit 합집합이어야 합니다. 이것이 ribbon/staircase 강제입니다.

따라서 leaf 병합 문제는 단순 counting 문제가 아니라 다음 조건을 동시에 만족하는 구조 문제입니다.

1. old colors는 여전히 단일순환이어야 한다.
2. leaf colors는 충분한 (x)-read를 donation 받아야 한다.
3. donation support는 RF2-closed ribbon이어야 한다.
4. leaf donated-orbit graph는 spanning connected이어야 한다.
5. (z=(z_0,z_1))-plane holonomy가 (m^2)-cycle을 만들어야 한다.
6. parity ledger를 맞추기 위해 홀수 개의 3색 이상 wild seam이 필요하다.

현재 탐색이 old cyclicity와 parity는 맞추지만 leaf가 (15,7) 같은 작은 cycle floor에서 멈추는 것은 자연스럽습니다. 어려운 것은 old가 아니라 leaf holonomy입니다.

---

# 7. 병목의 정확한 수학적 형태

leaf return을 skew product처럼 보면 대략

[
(x,z)\mapsto (T x,\ A_x z)
]

입니다. 여기서 (x)-base graph가 하나의 orbit을 가져도, 전체가 단일순환이 되려면 base 한 바퀴 후의 (z)-holonomy

[
A_{T^{K-1}x}\cdots A_{Tx}A_x
]

가 (Z=(\mathbb Z/m)^2) 위에서 primitive해야 합니다.

그런데 순수 translation은 (Z)에서 order가 최대 (m)입니다. (m^2)-cycle을 얻으려면 product rotor가 아니라 carry/snake/rail-seam류의 비선형 또는 piecewise holonomy가 필요합니다.

따라서 병목은 다음 한 문장으로 표현할 수 있습니다.

[
\boxed{
\text{RF2-closed donation ribbons 위에서 }z\text{-holonomy를 }m^2\text{-primitive로 만드는 splice word가 없다.}
}
]

아직 “없다”가 증명된 것은 아니고, “아직 구성되지 않았다”입니다.

---

# 8. 증명을 무조건화하려면 필요한 최소 산출물

가장 경제적인 산출물은 다음입니다.

## 산출물 A: conjugate (7\to9) repair theorem

정리 형태:

> For every even (m\ge4), given the certified (D7(m))-type chain input, there exists a root-flat (D9(m)) schedule such that all 9 color returns are single (m^8)-cycles, the old colors are cyclic but not necessarily pointwise lifts, and the output carries the ordinary paired-growth interface.

이 정리가 나오면 전체 proof route가 다시 살아날 가능성이 큽니다.

단, 이 theorem은 반드시 다음을 포함해야 합니다.

* parity-changing wild seam;
* RF2-closed donation ribbons;
* leaf donated graph spanning connectedness;
* (z)-holonomy primitivity;
* old colors single-cycle preservation;
* output interface for paired growth.

## 산출물 B: 직접 (\HED(9,m)) family

chained (7\to9)를 완전히 우회하려면 직접 (D9) family를 만들 수 있습니다.

필요한 형태:

[
\HED(9,m)\quad\text{for every even }m\ge4.
]

그러면 이후에는 ordinary paired growth만 쓰면 됩니다. 하지만 (m=4,6) finite certificate만으로는 부족합니다. high-even (m>9)와 (m=8)도 처리해야 하므로, 실제로는 uniform (D9) construction이 필요합니다.

## 산출물 C: rail-seam 고차원 odd propagation

D3 rail-seam 문법을 고차원화하여 홀수 차원 전파를 새로 만들 수도 있습니다. 이 경우 chained branch 전체를 버릴 수 있습니다.

이 방향의 첫 질문은:

[
D3\text{ rail-seam에서 }d\text{에 일양적인 성분과 아닌 성분은 무엇인가?}
]

입니다.

---

# 9. 원고 수정 관점의 권고

현재 원고는 다음처럼 정리해야 합니다.

## 반드시 삭제/강등

* `prop:chained-two-hole`의 현재 증명.
* `lem:growth-projection-discharge`의 endpoint-boundary version.
* “low-modulus (D7) finite input이 (\HED(7,4)), (\HED(7,6))를 growth-usable하게 공급한다”는 무조건적 주장.
* final induction의 `m=4,6`, (d\ge9) closure 주장.
* odd high-even (D\ge9) closure 주장, 현재 chained (7\to9)에 의존하는 형태.

## 유지 가능

* root-flat criterion.
* D3 base.
* phase doubling, 별도 검증된 범위에서.
* D5 anchor/reset.
* D7 pointwise certificates.
* parity ledger subsection.
* budget kill theorem subsection.
* endpoint-collision correction lemma.
* G7 failures를 정직하게 기록한 certificate appendix.

## 새로 넣어야 할 중심 절

개정본의 핵심 서사는 다음이어야 합니다.

> The old chained (7\to9) growth is impossible under pointwise preservation. The obstruction is not merely computational: parity and read budget give two structural reasons. Therefore the remaining task is a conjugate repair in which old colors remain cyclic but donate (x)-reads through RF2-closed ribbons, and the leaf holonomy becomes primitive on the (z)-plane.

이렇게 쓰면 현재 상태가 “실패한 증명”이 아니라 “폐기된 경로와 살아 있는 병목을 분리한 연구 상태”가 됩니다.

---

# 최종 감사 판정

[
\boxed{
\textbf{전체 theorem: 현재 조건부.}
}
]

[
\boxed{
\textbf{기존 chained }7\to9\textbf{ proof: 반증/폐기.}
}
]

[
\boxed{
\textbf{D7(4), D7(6) pointwise bases: 확정.}
}
]

[
\boxed{
\textbf{Parity ledger, budget kill: 무조건적 정리.}
}
]

[
\boxed{
\textbf{현재 병목: conjugate leaf 병합, 즉 RF2-closed donation ribbon + primitive }z\textbf{-holonomy.}
}
]

따라서 지금의 proof program은 “마지막 finite check 몇 개를 고치면 닫히는 상태”가 아닙니다. 정확히는 기존 보존형 chained 성장 전략이 죽었고, 전체 정리를 무조건화하려면 **새로운 (7\to9) repair 또는 chained 없는 odd propagation**이 필요합니다.
