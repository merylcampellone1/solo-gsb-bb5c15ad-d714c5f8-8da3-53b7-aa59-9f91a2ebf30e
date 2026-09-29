FROM node:20-alpine

ENV NODE_ENV=production \
    PORT=3000 \
    DATA_DIR=/app/data

WORKDIR /app

# 先装依赖，充分利用镜像层缓存
COPY package.json package-lock.json* ./
RUN npm install --omit=dev

COPY server.js ./
COPY public ./public

# 数据目录（音频与会话仅保存在本机/容器卷中）
RUN mkdir -p /app/data && chown -R node:node /app
USER node

EXPOSE 3000

CMD ["node", "server.js"]
