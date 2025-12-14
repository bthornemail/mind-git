# Navier-Stokes Paper Submission Checklist

## Phase 1: Pre-Submission Preparation (2-3 weeks)

### Code Validation ✅
- [ ] Run conservation law tests (mass, momentum, energy)
- [ ] Verify scalar field conservation
- [ ] Test adaptive refinement behavior
- [ ] Benchmark performance (100, 1K, 10K cells)
- [ ] Document test results in appendix

### Figures to Create 📊
- [ ] **Figure 1:** Voronoi mesh visualization (before/after refinement)
- [ ] **Figure 2:** Velocity field streamlines for Test Case 1
- [ ] **Figure 3:** Scalar field diffusion comparison (numerical vs analytical)
- [ ] **Figure 4:** Conservation law verification plots (mass, momentum, energy vs time)
- [ ] **Figure 5:** Adaptive refinement progression (mesh resolution over time)
- [ ] **Figure 6:** Performance scaling (cells vs computation time)

### Tables to Create 📋
- [ ] **Table 1:** Physical parameters summary
- [ ] **Table 2:** Conservation error quantification
- [ ] **Table 3:** Performance benchmarks
- [ ] **Table 4:** Comparison with existing codes (AREPO, DISCO, etc.)

### Code Cleanup 🧹
- [ ] Add comprehensive code comments
- [ ] Write unit tests for each major function
- [ ] Create example usage scripts
- [ ] Set up GitHub repository (public)
- [ ] Add MIT or Apache 2.0 license
- [ ] Create README with installation instructions

### Manuscript Polish ✍️
- [ ] Convert markdown to LaTeX
- [ ] Proofread for typos and grammar
- [ ] Check all equation numbering
- [ ] Verify all references are complete
- [ ] Add acknowledgments section
- [ ] Get colleague review (if available)

---

## Phase 2: arXiv Preprint (Week 4)

### arXiv Submission
- [ ] Create account at https://arxiv.org
- [ ] Choose category: physics.comp-ph (Computational Physics)
- [ ] Secondary categories:
  - physics.flu-dyn (Fluid Dynamics)
  - astro-ph.IM (Instrumentation and Methods for Astrophysics)
- [ ] Upload LaTeX source + figures
- [ ] Submit for review

### arXiv Requirements
- [ ] Abstract < 1920 characters
- [ ] No identifying information in manuscript (for journal submissions later)
- [ ] Figures in PDF or PNG format
- [ ] All references properly formatted

---

## Phase 3: Journal Submission (Week 5-6)

### Target Journals (in order of preference)

#### Option 1: Journal of Computational Physics ⭐⭐⭐⭐⭐
- **Impact Factor:** 4.0
- **Acceptance Rate:** ~30%
- **Review Time:** 2-4 months
- **Submission:** https://www.editorialmanager.com/jcomp/
- **Requirements:**
  - [ ] LaTeX using Elsevier template
  - [ ] Graphical abstract (single figure)
  - [ ] Highlights (3-5 bullet points, 85 chars each)
  - [ ] Cover letter explaining novelty

#### Option 2: Computer Physics Communications ⭐⭐⭐⭐⭐
- **Impact Factor:** 6.3
- **Acceptance Rate:** ~25%
- **Review Time:** 3-5 months
- **Submission:** https://www.editorialmanager.com/comphy/
- **Requirements:**
  - [ ] Code must be publicly available (GitHub ✓)
  - [ ] Software metapaper format
  - [ ] Installation/usage documentation

#### Option 3: SIAM Journal on Scientific Computing ⭐⭐⭐⭐
- **Impact Factor:** 3.1
- **Acceptance Rate:** ~35%
- **Review Time:** 2-3 months
- **Submission:** https://www.siam.org/publications/journals/siam-journal-on-scientific-computing-sisc
- **Requirements:**
  - [ ] SIAM LaTeX template
  - [ ] Algorithmic rigor emphasized
  - [ ] Mathematical proofs preferred

---

## Phase 4: Outreach (Parallel with submission)

### Email Template for Professors
- [ ] Identify 5-10 computational physics professors
- [ ] Find professors working on:
  - Moving mesh methods
  - Computational fluid dynamics
  - Adaptive mesh refinement
  - Multi-physics simulations
- [ ] Send personalized emails (template below)
- [ ] Follow up after 1 week if no response

### Academic Networking
- [ ] Post on Twitter/X with #CompPhys #CFD hashtags
- [ ] Share on ResearchGate
- [ ] Post to r/CFD and r/compsci on Reddit
- [ ] Join Computational Physics Discord/Slack channels

---

## Phase 5: Response to Reviewers (3-4 months later)

### When Reviews Arrive
- [ ] Read all reviews carefully
- [ ] Categorize comments: major, minor, editorial
- [ ] Draft point-by-point response
- [ ] Make manuscript revisions
- [ ] Highlight changes in revised manuscript
- [ ] Resubmit within deadline (usually 2-3 months)

### Common Review Concerns to Prepare For
- "Comparison with existing codes needed" → Prepare AREPO/DISCO benchmarks
- "Higher-order methods should be used" → Discuss future work or add RK4
- "Validation insufficient" → Add more test cases
- "Novelty unclear" → Emphasize multi-physics coupling

---

## Timeline Summary

| Week | Task | Deliverable |
|------|------|-------------|
| 1-2 | Run validation tests, create figures | Test results, 6 figures |
| 3 | Write LaTeX version, create tables | LaTeX manuscript |
| 4 | Submit to arXiv, set up GitHub | arXiv preprint, public code |
| 5 | Prepare journal submission materials | Cover letter, highlights |
| 6 | Submit to journal | Submission confirmation |
| 14-22 | Respond to reviews | Revised manuscript |
| 24-30 | Publication! | DOI and citation |

---

## Success Metrics

### Minimum Viable Publication
- [ ] arXiv preprint published
- [ ] Code publicly available on GitHub
- [ ] At least 1 colleague review

### Strong Publication
- [ ] Accepted to JCP or CPC
- [ ] 3+ citations within first year
- [ ] Code used by another research group

### Excellent Publication
- [ ] Accepted to top journal (JCP, CPC)
- [ ] 10+ citations within 2 years
- [ ] Invited talk at conference
- [ ] Collaboration offers from other groups

---

## Resources

### LaTeX Templates
- Journal of Computational Physics: https://www.elsevier.com/authors/policies-and-guidelines/latex-instructions
- SIAM: https://www.siam.org/publications/journals/about-siam-journals/information-for-authors
- arXiv: https://arxiv.org/help/submit_tex

### Visualization Tools
- Python matplotlib for plots
- ParaView for 3D mesh visualization
- Gnuplot for quick plots
- TikZ for LaTeX diagrams

### Writing Guides
- "How to Write a Great Research Paper" by Simon Peyton Jones
- "The Craft of Scientific Writing" by Michael Alley
- "Writing Science" by Joshua Schimel

---

## Emergency Contacts

If you get stuck, reach out to:
- arXiv support: help@arxiv.org
- Journal editorial office (see journal website)
- Local university computational science department
- Online: Computational Science StackExchange

---

**Last Updated:** 2025-12-13
**Status:** Ready to begin Phase 1
