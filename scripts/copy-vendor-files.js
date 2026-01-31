import { copyFileSync, mkdirSync } from 'fs';
import { dirname } from 'path';
import { fileURLToPath } from 'url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const projectRoot = dirname(__dirname);

const filesToCopy = [
  {
    src: 'node_modules/z3-solver/build/z3-built.js',
    dest: 'public/z3-built.js'
  },
  {
    src: 'node_modules/z3-solver/build/z3-built.wasm',
    dest: 'public/z3-built.wasm'
  },
  {
    src: 'node_modules/coi-serviceworker/coi-serviceworker.js',
    dest: 'public/coi-serviceworker.js'
  }
];

mkdirSync(`${projectRoot}/public`, { recursive: true });

filesToCopy.forEach(({ src, dest }) => {
  const srcPath = `${projectRoot}/${src}`;
  const destPath = `${projectRoot}/${dest}`;
  
  try {
    copyFileSync(srcPath, destPath);
    console.log(`✓ Copied ${src} → ${dest}`);
  } catch (error) {
    console.error(`✗ Failed to copy ${src}:`, error.message);
    process.exit(1);
  }
});

console.log('✓ All vendor files copied successfully');
