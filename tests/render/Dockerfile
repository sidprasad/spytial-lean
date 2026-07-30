# Pins every pixel-affecting input for the baselines: browser, fonts, OS.
# Digest-pinned so a rebuilt upstream tag can't change what a baseline means.
# = mcr.microsoft.com/playwright:v1.62.0-noble; bump in lockstep with
# @playwright/test in pnpm-workspace.yaml, which refuses mismatched browsers.
FROM mcr.microsoft.com/playwright@sha256:baed2032d533817f3dbe6425de795788430ba345e819a1201337009ba17c9d07

# spytial-core asks for 'Atkinson Hyperlegible' and @imports it from Google
# Fonts. Installing it locally lets `--network none` hold without changing the
# typeface; this image's own sans-serif is a CJK face, so fallback is no option.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      fonts-atkinson-hyperlegible=0.0~git20210430.1cb3116-2 \
 && rm -rf /var/lib/apt/lists/*
