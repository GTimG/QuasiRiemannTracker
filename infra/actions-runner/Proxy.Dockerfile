FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac

RUN apt-get update \
    && apt-get install -y --no-install-recommends python3 util-linux \
    && rm -rf /var/lib/apt/lists/*

ENV PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1
COPY --chmod=0444 proxy.py /opt/runner-proxy.py
USER 10002:10002
EXPOSE 3128
HEALTHCHECK --interval=30s --timeout=5s --start-period=5s --retries=3 \
    CMD ["python3", "-c", "import socket; s = socket.create_connection(('127.0.0.1', 3128), 2); s.sendall(b'GET / HTTP/1.1\\r\\nHost: healthcheck\\r\\n\\r\\n'); assert s.recv(128).startswith(b'HTTP/1.1 403 ')"]
ENTRYPOINT ["/usr/bin/setpriv", "--no-new-privs", "python3", "/opt/runner-proxy.py"]
