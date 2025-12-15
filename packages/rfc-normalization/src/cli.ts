#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import { glob } from 'glob';
import { readFile, writeFile } from 'fs/promises';
import { RFCNormalizer } from './rfc-normalizer.js';
import { PhaseManager } from './phase-manager.js';

const program = new Command();
const normalizer = new RFCNormalizer();
const phaseManager = new PhaseManager();

program
  .name('rfc-normalization')
  .description('RFC constraint enforcement and metaphysical language normalization')
  .version('1.0.0');

// Check command
program
  .command('check')
  .description('Check RFC compliance of files')
  .option('-f, --file <path>', 'Specific file to check')
  .option('-p, --pattern <pattern>', 'Glob pattern for files to check', '**/*.md')
  .option('--fail-on-violations', 'Exit with error code on violations', false)
  .option('--red-flags', 'Include red flag detection', true)
  .action(async (options) => {
    console.log(chalk.blue('🔍 RFC Compliance Check'));
    console.log('='.repeat(50));

    try {
      const files = options.file 
        ? [options.file]
        : await glob(options.pattern, { ignore: 'node_modules/**' });

      if (files.length === 0) {
        console.log(chalk.yellow('No files found to check.'));
        return;
      }

      let totalViolations = 0;
      let totalRedFlags = 0;
      let compliantFiles = 0;

      for (const file of files) {
        try {
          const content = await readFile(file, 'utf-8');
          const result = normalizer.validateContent(content);
          
          console.log(`\n📄 ${file}`);
          console.log('-'.repeat(file.length + 3));

          if (result.valid) {
            console.log(chalk.green('✅ RFC Compliant'));
            compliantFiles++;
          } else {
            console.log(chalk.red('❌ RFC Violations Detected'));
          }

          if (result.violations.length > 0) {
            console.log(`\n📊 Violations: ${result.violations.length}`);
            result.violations.forEach(violation => {
              const icon = violation.severity === 'error' ? '🚨' : 
                          violation.severity === 'warning' ? '⚠️' : 'ℹ️';
              console.log(`  ${icon} [${violation.section}] ${violation.message}`);
              if (violation.line) {
                console.log(`     Line ${violation.line}`);
              }
            });
            totalViolations += result.violations.length;
          }

          if (options.redFlags) {
            const redFlagReport = normalizer['redFlagDetector'].detectRedFlags(content);
            if (redFlagReport.flags.length > 0) {
              console.log(`\n🚩 Red Flags: ${redFlagReport.flags.length}`);
              redFlagReport.flags.forEach(flag => {
                const icon = flag.severity === 'error' ? '🚨' : '⚠️';
                console.log(`  ${icon} [${flag.section}] ${flag.message}`);
                if (flag.line) {
                  console.log(`     Line ${flag.line}`);
                }
              });
              totalRedFlags += redFlagReport.flags.length;
            }
          }

        } catch (error) {
          console.log(chalk.red(`❌ Error reading ${file}: ${error}`));
        }
      }

      // Summary
      console.log('\n' + '='.repeat(50));
      console.log(chalk.blue('📈 Summary'));
      console.log(`Files checked: ${files.length}`);
      console.log(`Compliant files: ${chalk.green(compliantFiles)}`);
      console.log(`Total violations: ${chalk.red(totalViolations)}`);
      console.log(`Total red flags: ${chalk.red(totalRedFlags)}`);

      if (options.failOnViolations && (totalViolations > 0 || totalRedFlags > 0)) {
        process.exit(1);
      }

    } catch (error) {
      console.error(chalk.red(`Error: ${error}`));
      process.exit(1);
    }
  });

// Normalize command
program
  .command('normalize')
  .description('Normalize files to comply with RFC constraints')
  .option('-f, --file <path>', 'Specific file to normalize')
  .option('-p, --pattern <pattern>', 'Glob pattern for files to normalize', '**/*.md')
  .option('--backup', 'Create backup of original files', true)
  .option('--dry-run', 'Show changes without applying them', false)
  .action(async (options) => {
    console.log(chalk.blue('🔧 RFC Normalization'));
    console.log('='.repeat(50));

    try {
      const files = options.file 
        ? [options.file]
        : await glob(options.pattern, { ignore: 'node_modules/**' });

      if (files.length === 0) {
        console.log(chalk.yellow('No files found to normalize.'));
        return;
      }

      for (const file of files) {
        try {
          const content = await readFile(file, 'utf-8');
          const result = normalizer.normalizeContent(content, {
            addDomainQualifiers: true,
            applyStructuralFixes: true,
            normalizeLanguage: true
          });
          
          console.log(`\n📄 ${file}`);
          console.log('-'.repeat(file.length + 3));

          if (result.changes.length === 0) {
            console.log(chalk.green('✅ Already compliant'));
            continue;
          }

          console.log(`🔄 Changes applied: ${result.changes.length}`);
          result.changes.forEach((change, index) => {
            console.log(`  ${index + 1}. ${change.description || change.type}`);
            if ('original' in change && 'replacement' in change) {
              console.log(`     "${change.original}" → "${change.replacement}"`);
            }
          });

          if (result.violations.length > 0) {
            console.log(`\n⚠️  Remaining violations: ${result.violations.length}`);
          }

          if (!options.dryRun) {
            if (options.backup) {
              const backupPath = `${file}.backup.${Date.now()}`;
              await writeFile(backupPath, content);
              console.log(`💾 Backup created: ${backupPath}`);
            }
            
            await writeFile(file, result.normalized);
            console.log(chalk.green('✅ File normalized'));
          } else {
            console.log(chalk.yellow('🔍 Dry run - changes not applied'));
          }

        } catch (error) {
          console.log(chalk.red(`❌ Error processing ${file}: ${error}`));
        }
      }

    } catch (error) {
      console.error(chalk.red(`Error: ${error}`));
      process.exit(1);
    }
  });

// Report command
program
  .command('report')
  .description('Generate comprehensive compliance report')
  .option('-f, --file <path>', 'Specific file to analyze')
  .option('-p, --pattern <pattern>', 'Glob pattern for files to analyze', '**/*.md')
  .option('--output <path>', 'Output file for report (JSON format)')
  .action(async (options) => {
    console.log(chalk.blue('📊 Compliance Report Generation'));
    console.log('='.repeat(50));

    try {
      const files = options.file 
        ? [options.file]
        : await glob(options.pattern, { ignore: 'node_modules/**' });

      const report: any = {
        timestamp: new Date().toISOString(),
        filesAnalyzed: files.length,
        results: [],
        summary: {
          totalViolations: 0,
          totalRedFlags: 0,
          compliantFiles: 0,
          averageScore: 0
        }
      };

      for (const file of files) {
        try {
          const content = await readFile(file, 'utf-8');
          const complianceReport = normalizer.generateComplianceReport(content);
          
          const fileResult = {
            file,
            overall: complianceReport.overall,
            score: complianceReport.score,
            violations: complianceReport.violations.length,
            redFlags: complianceReport.redFlagReport.summary.total,
            recommendations: complianceReport.recommendations
          };

          report.results.push(fileResult);
          report.summary.totalViolations += fileResult.violations;
          report.summary.totalRedFlags += fileResult.redFlags;
          
          if (complianceReport.overall === 'COMPLIANT') {
            report.summary.compliantFiles++;
          }

        } catch (error) {
          console.log(chalk.red(`❌ Error analyzing ${file}: ${error}`));
        }
      }

      report.summary.averageScore = report.results.length > 0 
        ? report.results.reduce((sum: number, r: any) => sum + r.score, 0) / report.results.length 
        : 0;

      // Display summary
      console.log(`\n📈 Report Summary`);
      console.log(`Files analyzed: ${report.filesAnalyzed}`);
      console.log(`Compliant files: ${chalk.green(report.summary.compliantFiles)}`);
      console.log(`Total violations: ${chalk.red(report.summary.totalViolations)}`);
      console.log(`Total red flags: ${chalk.red(report.summary.totalRedFlags)}`);
      console.log(`Average compliance score: ${report.summary.averageScore.toFixed(1)}/100`);

      // Save report if requested
      if (options.output) {
        await writeFile(options.output, JSON.stringify(report, null, 2));
        console.log(`\n💾 Report saved to: ${options.output}`);
      }

    } catch (error) {
      console.error(chalk.red(`Error: ${error}`));
      process.exit(1);
    }
  });

// Phase command
program
  .command('phase')
  .description('Manage development phases')
  .option('--status', 'Show current phase status')
  .option('--transition <phase>', 'Transition to specified phase')
  .option('--reason <reason>', 'Reason for phase transition')
  .action(async (options) => {
    console.log(chalk.blue('🎯 Phase Management'));
    console.log('='.repeat(50));

    try {
      if (options.status) {
        const summary = phaseManager.getPhaseSummary();
        console.log(`Current phase: ${chalk.green(summary.current)}`);
        console.log(`Is complete: ${await summary.isComplete ? chalk.green('Yes') : chalk.red('No')}`);
        
        if (summary.nextPossible.length > 0) {
          console.log(`Next possible phases: ${summary.nextPossible.join(', ')}`);
        }

        console.log('\nCompletion requirements:');
        summary.completionRequirements.forEach((req, index) => {
          console.log(`  ${index + 1}. ${req}`);
        });

        console.log('\nPhase history:');
        summary.history.forEach(entry => {
          console.log(`  ${entry.timestamp.toISOString()}: ${entry.phase} - ${entry.reason}`);
        });
      }

      if (options.transition) {
        const reason = options.reason || 'Manual transition via CLI';
        const result = await phaseManager.transitionTo(options.transition, reason);
        
        if (result.allowed) {
          console.log(chalk.green(`✅ ${result.reason}`));
        } else {
          console.log(chalk.red(`❌ ${result.reason}`));
          if (result.required) {
            console.log('\nRequired actions:');
            result.required.forEach((req: string, index: number) => {
              console.log(`  ${index + 1}. ${req}`);
            });
          }
        }
      }

    } catch (error) {
      console.error(chalk.red(`Error: ${error}`));
      process.exit(1);
    }
  });

// Parse command line arguments
program.parse();