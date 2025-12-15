#!/bin/bash
# Test OpenAI API with single image

source ../../../../.env

curl https://api.openai.com/v1/images/generations \
  -H "Content-Type: application/json" \
  -H "Authorization: Bearer $META_GIT_OPEN_API_KEY" \
  -d '{
    "model": "dall-e-3",
    "prompt": "A simple test image: npm logo on dark background with text mind-git v1.1.0",
    "size": "1024x1024",
    "quality": "standard",
    "n": 1
  }'
