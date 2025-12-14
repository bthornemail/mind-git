import { Notice } from 'obsidian';
import { execSync } from 'child_process';

/**
 * Utility class for resolving mind-git CLI executable paths
 * Supports multiple environments and fallback strategies
 */
export class PathResolver {
  private static cachedPath: string | null = null;
  
  /**
   * Resolve CLI path using multiple strategies
   */
  static resolveCLIPath(): string {
    if (this.cachedPath) {
      return this.cachedPath;
    }
    
    const candidates = [
      // Development environment
      '/home/main/devops/mind-git/bin/mind-git-simple.cjs',
      '/home/main/devops/mind-git/bin/mind-git.cjs',
      
      // Local installation
      './node_modules/mind-git/bin/mind-git.cjs',
      './node_modules/mind-git/bin/mind-git-simple.cjs',
      
      // Global installation via npx
      'npx mind-git',
      
      // Environment variable override
      process.env.MIND_GIT_CLI_PATH,
      
      // System-wide installation
      'mind-git'
    ].filter(Boolean); // Remove null/undefined
  
    for (const candidate of candidates) {
      if (this.isValidPath(candidate)) {
        this.cachedPath = candidate;
        console.log(`✅ CLI path resolved: ${candidate}`);
        return candidate;
      }
    }
    
    // Default fallback
    const fallback = '/home/main/devops/mind-git/bin/mind-git-simple.cjs';
    console.warn(`⚠️ Using fallback CLI path: ${fallback}`);
    this.cachedPath = fallback;
    return fallback;
  }
  
  /**
   * Check if a CLI path is valid and executable
   */
  private static isValidPath(path: string): boolean {
    try {
      if (path.startsWith('npx') || !path.includes('/')) {
        // Test npx or system command
        execSync(`${path} version`, { 
          stdio: 'ignore', 
          timeout: 5000 
        });
        return true;
      } else {
        // Test file path
        const fs = require('fs');
        return fs.existsSync(path) && fs.accessSync(path, fs.constants.F_OK);
      }
    } catch (error) {
      return false;
    }
  }
  
  /**
   * Test CLI availability and version
   */
  static async testCLI(): Promise<{ available: boolean; version?: string; error?: string }> {
    try {
      const cliPath = this.resolveCLIPath();
      const version = execSync(`${cliPath} version`, { 
        encoding: 'utf8',
        timeout: 10000 
      });
      
      return {
        available: true,
        version: version.trim()
      };
    } catch (error) {
      return {
        available: false,
        error: error.message
      };
    }
  }
  
  /**
   * Clear cached path (useful for testing or configuration changes)
   */
  static clearCache(): void {
    this.cachedPath = null;
  }
  
  /**
   * Get CLI command with proper node execution
   */
  static getCLICommand(): string {
    const path = this.resolveCLIPath();
    
    // Add node prefix for .cjs files
    if (path.endsWith('.cjs') && !path.startsWith('npx')) {
      return `node "${path}"`;
    }
    
    return path;
  }
}