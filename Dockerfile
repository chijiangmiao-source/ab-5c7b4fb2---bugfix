# syntax=docker/dockerfile:1
# 多阶段构建:
#   app    —— 运行态镜像(零第三方依赖,仅标准库)
#   verify —— 验证镜像,FROM app 阶段:构建 verify 即强制复核 app 镜像可构建,
#             并在其中携带代码测试与 HTTP 冒烟脚本
FROM python:3.11-slim AS app
ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PORT=8080 \
    APP_VERSION=1.0.0
WORKDIR /srv
COPY app ./app
EXPOSE 8080
CMD ["python", "-m", "app.server"]

FROM app AS verify
COPY tests ./tests
COPY scripts ./scripts
CMD ["sh", "-c", "python -m unittest discover -s tests -t . && python scripts/smoke.py"]
