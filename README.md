# Lattice Paths em Rocq — LC1 2026/1 (UnB)

Formalização e prova, no assistente **Rocq**, da
**equivalência entre caminhos em uma grade cartesiana** (*lattice paths*).
Um caminho usa apenas passos para a **direita** (`Right`) e para **cima** (`Up`).
Provamos que caminhos equivalentes por **permutação de passos** têm o **mesmo
comprimento** e o **mesmo ponto final** — com a comutatividade `R;U ≡ U;R` como
caso emblemático.

> Disciplina: Lógica Computacional 1 — 2026/1 — Prof. Flávio L. C. de Moura.

## Estrutura do repositório

| Arquivo | Descrição |
|---|---|
| `CaminhosReticulado.v` | Provas. |

## Como compilar

```sh
coqc CaminhosReticulado.v
```

## Resultados formalizados

- `aplica_passo_comuta` — passos comutam (núcleo geométrico).
- `equiv_mesmo_comprimento` — caminhos equivalentes têm o mesmo comprimento.
- `equiv_mesmo_destino` — caminhos equivalentes têm o mesmo ponto final.
- `equiv_preserva` — teorema principal (comprimento **e** ponto final).
- `equiv_mesmo_ponto_final` — corolário a partir da origem.

## Autores

- Victor Yan Martinez de Ávila — 241032994
- Pedro do Nascimento Holanda — 232005998
