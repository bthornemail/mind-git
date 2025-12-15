#!/usr/bin/env node

/**
 * Generate all visual assets for mind-git v1.1.0 launch
 * Uses OpenAI DALL-E 3 to create professional images
 */

const fs = require('fs');
const path = require('path');
const https = require('https');

// Load environment variables
require('dotenv').config({ path: path.join(__dirname, '../../../../.env') });

const OPENAI_API_KEY = process.env.META_GIT_OPEN_API_KEY || process.env.OPENAI_API_KEY;

if (!OPENAI_API_KEY) {
  console.error('❌ ERROR: No OpenAI API key found in .env');
  console.error('   Set META_GIT_OPEN_API_KEY or OPENAI_API_KEY');
  process.exit(1);
}

// Image generation prompts
const PROMPTS = [
  {
    name: '01-launch-banner',
    size: '1792x1024',
    prompt: `A modern, professional tech banner for a programming tool launch. Dark theme with deep blue (#0f172a) background. Center: glowing network of connected nodes forming a spatial diagram, with mathematical symbols (∑, ∫, π) integrated into node connections. Left side: subtle npm logo in red. Right side: "mind-git v1.1.0" in clean sans-serif font. Floating mathematical equations in the background (polynomial notation over F₂). Holographic/neon effect on node connections. Professional, clean, minimal. Style: Modern tech startup, slightly futuristic but grounded.`
  },
  {
    name: '02-npm-package-card',
    size: '1024x1024',
    prompt: `A square social media card for an npm package release. Dark background (#1a1a1a). Center: Large npm logo in red with package name "mind-git" below in white monospace font. Top text: "NOW AVAILABLE". Bottom: "npm install -g mind-git" in terminal-style text with green cursor. Surrounding the center: floating abstract representations of spatial nodes and edges, glowing softly. Subtle grid pattern in background. Clean, professional, developer-focused.`
  },
  {
    name: '03-timeline-infographic',
    size: '1792x1024',
    prompt: `An educational infographic showing a timeline from 628 AD to 2025. Horizontal timeline with elegant serif font for dates. Each milestone has: 628 AD: Portrait-style illustration of ancient Indian mathematician (Brahmagupta) with "2D Complex Numbers" label, 1748: Leonhard Euler with powdered wig, "4D Quaternions" label, 1928: Modern-era mathematician (Heinrich Degen), "8D Octonions" label, 1960: John Frank Adams with blackboard showing proof, "8D Limit Theorem", 2025: Modern laptop/terminal showing "mind-git v1.1.0". Each point connected by flowing mathematical formula ribbon. Color gradient from warm ancient (sepia) to cool modern (blue). Professional, educational, museum-quality style.`
  },
  {
    name: '04-architecture-diagram',
    size: '1792x1024',
    prompt: `A technical architecture diagram in modern infographic style. Three main sections flowing left to right: LEFT: "Input" - Abstract canvas/diagram with colorful nodes and connecting lines, CENTER: "Compiler" - Layered rings showing transformation process, with mathematical symbols (F₂, polynomials) integrated, RIGHT: "Output" - Multiple terminal windows showing code in different colors (JS in yellow, TypeScript in blue, Racket in purple). Connected by glowing data streams. Dark background with neon accents. Clean, professional, SaaS product style. Include small "✓ Verified" checkmarks.`
  },
  {
    name: '05-spatial-concept-art',
    size: '1792x1024',
    prompt: `Abstract concept art showing the transformation of space into code. Left half: 3D wireframe space with floating geometric nodes (spheres, cubes) connected by glowing lines, reminiscent of constellation maps. Right half: The same structure represented as flowing lines of code, with the geometry "unfolding" into text. Center: Transition zone where 3D geometry becomes 2D code. Color palette: Deep blues, purples, and cyan glows on black background. Ethereal, slightly sci-fi but grounded. Style: Think "Tron meets mathematical textbook".`
  },
  {
    name: '06-compiler-pipeline',
    size: '1024x1024',
    prompt: `A flowing pipeline diagram in isometric 3D style. Five connected platforms/stages: Stage 1: "Canvas JSON" - File icon with spatial diagram preview, Stage 2: "Parser" - Gear mechanisms analyzing nodes, Stage 3: "AST" - Tree structure growing upward, Stage 4: "Code Gen" - Assembly line producing code scrolls, Stage 5: "Verified" - Checkmark seal with mathematical symbols. Connected by conveyor belts carrying glowing data packets. Clean isometric 3D render, slight cartoon style but professional. Light blue and purple color scheme. White background.`
  },
  {
    name: '07-math-foundation-pyramid',
    size: '1024x1024',
    prompt: `A layered pyramid/stack diagram showing mathematical foundations. Each layer is a transparent glass-like platform with glowing edges: BOTTOM: "Brahmagupta 628 AD" - 2D complex plane visualization, LAYER 2: "Euler 1748" - 4D quaternion sphere, LAYER 3: "Degen 1928" - 8D octonion structure (abstract geometric), LAYER 4: "Adams 1960" - Dimensional limit proof (formula on transparent surface), TOP: "mind-git 2025" - Glowing terminal with code. Each layer connected by light beams. Floating mathematical formulas around the structure. Dark background with spotlight on pyramid. Professional, educational, slightly futuristic.`
  },
  {
    name: '08-youtube-thumbnail',
    size: '1280x720',
    prompt: `An eye-catching YouTube thumbnail template. Large text space in center reading "SPATIAL PROGRAMMING" in bold, impactful font. Background: Split design - left half shows abstract spatial diagram with glowing nodes, right half shows code editor with JavaScript. Vibrant colors: Electric blue (#0ea5e9), Purple (#a855f7), and bright highlights. High contrast, YouTube algorithm-friendly style. Professional but attention-grabbing.`
  },
  {
    name: '09-github-social-card',
    size: '1280x640',
    prompt: `A GitHub repository social preview card. Top: GitHub logo in corner. Center: Large "mind-git" in monospace font with terminal cursor. Below: "Visual Programming + Mathematical Verification". Background: Subtle pattern of connected nodes forming network topology, very faint. Color scheme: GitHub dark theme (#0d1117 background, #58a6ff blue accents). Bottom: Technology badges (TypeScript, Coq, npm). Clean, professional, developer-focused.`
  },
  {
    name: '10-announcement-hero',
    size: '1792x1024',
    prompt: `A celebratory hero image for product launch announcement. Center: Large 3D rendered npm cube with mind-git logo on faces, floating in space. Surrounding: Confetti-like mathematical symbols (∫, ∑, π, ∂) and small floating code snippets. Background: Gradient from dark blue to purple. Spotlight effect on npm cube. Small text below cube: "v1.1.0 - Now Available". Festive but professional tone. Clean, modern 3D render style.`
  }
];

// Download image from URL
function downloadImage(url, filepath) {
  return new Promise((resolve, reject) => {
    const file = fs.createWriteStream(filepath);
    https.get(url, response => {
      response.pipe(file);
      file.on('finish', () => {
        file.close();
        resolve(filepath);
      });
    }).on('error', err => {
      fs.unlink(filepath, () => {});
      reject(err);
    });
  });
}

// Generate single image
async function generateImage(prompt, name, size) {
  console.log(`\n🎨 Generating: ${name}`);
  console.log(`   Size: ${size}`);
  console.log(`   Prompt: ${prompt.substring(0, 80)}...`);

  const [width, height] = size.split('x');
  const apiSize = width === height ? '1024x1024' : '1792x1024';

  const requestData = JSON.stringify({
    model: 'dall-e-3',
    prompt: prompt,
    size: apiSize,
    quality: 'hd',
    n: 1
  });

  return new Promise((resolve, reject) => {
    const options = {
      hostname: 'api.openai.com',
      port: 443,
      path: '/v1/images/generations',
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${OPENAI_API_KEY}`,
        'Content-Length': requestData.length
      }
    };

    const req = https.request(options, res => {
      let data = '';

      res.on('data', chunk => {
        data += chunk;
      });

      res.on('end', async () => {
        try {
          const response = JSON.parse(data);

          if (response.error) {
            console.error(`   ❌ Error: ${response.error.message}`);
            reject(new Error(response.error.message));
            return;
          }

          const imageUrl = response.data[0].url;
          const filename = `${name}.png`;
          const filepath = path.join(__dirname, filename);

          console.log(`   ⬇️  Downloading...`);
          await downloadImage(imageUrl, filepath);
          console.log(`   ✅ Saved: ${filename}`);

          resolve(filepath);
        } catch (error) {
          console.error(`   ❌ Parse error:`, error.message);
          reject(error);
        }
      });
    });

    req.on('error', error => {
      console.error(`   ❌ Request error:`, error.message);
      reject(error);
    });

    req.write(requestData);
    req.end();
  });
}

// Main execution
async function main() {
  console.log('🚀 mind-git v1.1.0 - Image Generation');
  console.log('=====================================\n');
  console.log(`📦 Generating ${PROMPTS.length} professional images`);
  console.log(`💰 Estimated cost: $${(PROMPTS.length * 0.04).toFixed(2)} (HD quality)`);
  console.log(`⏱️  Estimated time: ${PROMPTS.length * 30} seconds\n`);

  const results = {
    success: [],
    failed: []
  };

  for (let i = 0; i < PROMPTS.length; i++) {
    const { name, prompt, size } = PROMPTS[i];

    try {
      const filepath = await generateImage(prompt, name, size);
      results.success.push({ name, filepath });

      // Rate limiting: Wait 2 seconds between requests
      if (i < PROMPTS.length - 1) {
        console.log('   ⏳ Waiting 2s for rate limit...');
        await new Promise(resolve => setTimeout(resolve, 2000));
      }
    } catch (error) {
      console.error(`   ❌ Failed: ${error.message}`);
      results.failed.push({ name, error: error.message });
    }
  }

  // Summary
  console.log('\n=====================================');
  console.log('📊 Generation Summary\n');
  console.log(`✅ Success: ${results.success.length}/${PROMPTS.length}`);
  console.log(`❌ Failed: ${results.failed.length}/${PROMPTS.length}`);

  if (results.success.length > 0) {
    console.log('\n✅ Generated Images:');
    results.success.forEach(({ name, filepath }) => {
      const stats = fs.statSync(filepath);
      const sizeKB = (stats.size / 1024).toFixed(1);
      console.log(`   - ${name}.png (${sizeKB} KB)`);
    });
  }

  if (results.failed.length > 0) {
    console.log('\n❌ Failed Images:');
    results.failed.forEach(({ name, error }) => {
      console.log(`   - ${name}: ${error}`);
    });
  }

  console.log('\n🎉 Image generation complete!');
  console.log('📁 Images saved to: dev-docs/Announcements/December/15/visuals/');
  console.log('\n⚠️  REMEMBER: Rotate your OpenAI API key NOW!');
  console.log('   Visit: https://platform.openai.com/api-keys\n');
}

// Run
main().catch(error => {
  console.error('💥 Fatal error:', error);
  process.exit(1);
});
