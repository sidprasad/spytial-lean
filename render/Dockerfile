# Digest-pinned so a rebuilt upstream tag can't change what a render means.
# = mcr.microsoft.com/playwright:v1.62.0-noble; bump with @playwright/test.
FROM mcr.microsoft.com/playwright@sha256:baed2032d533817f3dbe6425de795788430ba345e819a1201337009ba17c9d07

# spytial-core @imports this from Google Fonts; installing it locally lets
# `--network none` hold. The image's own sans-serif is CJK, so fallback is out.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      fonts-atkinson-hyperlegible=0.0~git20210430.1cb3116-2 \
 && rm -rf /var/lib/apt/lists/*
