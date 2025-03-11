#!/bin/bash

#Builds the image on two different platforms and pushes it to dockerhub
docker buildx build --platform linux/arm64,linux/amd64 -t \
	kayceesrk/fstar-devcontainer:latest --push -f Dockerfile.pinned .
