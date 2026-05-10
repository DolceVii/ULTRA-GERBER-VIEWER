# ULTRA GERBER VIEWER

**ULTRA GERBER VIEWER** is a high-performance **Gerber / Drill Viewer** with integrated **realistic 3D PCB visualization**, developed in **Pure Python 3 + PyQt6**.

The project is designed for real-world PCB inspection, CAM review, Gerber analysis and advanced visualization workflows — without using external Gerber rendering engines.

---

## Preview

Add your clean application screenshot here:

```markdown
![ULTRA GERBER VIEWER](screenshots/ui.png)
```

---

## Key Features

- Fast Gerber rendering
- Realistic 3D PCB visualization
- Multi-layer PCB inspection
- Excellon / NC Drill support
- Aperture macro support
- Region and polygon rendering
- Thermal relief rendering
- Copper, soldermask, silkscreen and drill visualization
- Measurement tool
- Professional dark user interface
- Custom raster/vector rendering pipeline
- Standalone desktop application
- No `gerbv`
- No external renderer

---

## Supported Formats

### Gerber

- RS-274X Gerber files
- Common KiCad Gerber exports
- Common Altium Gerber exports
- Common Proteus Gerber exports
- Copper, soldermask, paste, silkscreen, profile and mechanical layers

### Drill

- Excellon drill files
- NC Drill files
- Plated and non-plated hole visualization

---

## Technologies

- Python 3
- PyQt6
- Custom Gerber parser
- Custom Excellon parser
- Custom PCB rendering engine
- Real-time vector/raster rendering

---

## Installation

Clone the repository:

```bash
git clone https://github.com/DolceVii/ULTRA-GERBER-VIEWER.git
cd ULTRA-GERBER-VIEWER
```

Install dependencies:

```bash
pip install -r requirements.txt
```

---

## Run

```bash
python UltraView1.py
```

---

## Keyboard Controls

| Key | Action |
| --- | --- |
| `F` | Fit PCB to view |
| `C` | Center view |
| `M` | Measurement mode |
| `Esc` | Clear measurement / exit measurement mode |

---

## Project Goals

The goal of ULTRA GERBER VIEWER is to provide a modern PCB visualization tool focused on:

- fast Gerber/Drill inspection,
- realistic PCB rendering,
- CAM-style analysis,
- professional desktop usability,
- future expansion toward advanced PCB manufacturing checks.

---

## Roadmap

Planned / experimental ideas:

- Improved 3D PCB interaction
- STEP / 3D model integration
- GPU/OpenGL rendering backend
- Advanced CAM inspection tools
- DRC-style visualization
- ODB++ support
- AI-assisted PCB analysis
- High-resolution export engine

---

## Repository Structure

```text
ULTRA-GERBER-VIEWER/
├── assets/          # Logo, icons, splash screen and future UI resources
├── docs/            # Technical documentation
├── screenshots/     # Project screenshots
├── UltraView1.py    # Main application source file
├── requirements.txt # Python dependencies
├── LICENSE          # MIT License
└── README.md        # Project overview
```

---

## Status

This project is under active development. The current release is an early public version intended for testing, feedback and continuous improvement.

---

## Developer

**George Kourtidis**  
Electronic Engineer & Software Developer

---

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
