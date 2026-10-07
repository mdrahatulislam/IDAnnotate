IDAnnotate -- By Md.Rahatul Islam

Identity-aware video and image annotation desktop app (Tkinter + OpenCV + Pillow). Class and Individual ID are stored separately, so the same person keeps one persistent ID across a whole project.

git clone https://github.com/mdrahatulislam/IDAnnotate.git
cd IDAnnotate
pip install -r requirements.txt
python IDAnnotate.py

Features:
Open a video or an image folder and draw bounding boxes (move, resize, rotate)
Classes plus persistent Individual IDs
Track Forward with the ID locked, plus OpenCV auto-tracking
Save / load projects as JSON
Export YOLO, COCO and MOT
Export the annotated video (boxes + ID labels burned in); with ffmpeg on PATH it is saved as H.264 with the original audio


Shortcuts
Key	Action
Left / Right	Previous / next frame
Space	Play / pause
1-N	Select Individual ID
S	Save project
C	Copy previous frame
X	Clear frame
Delete	Delete selected box
Ctrl+E	Export annotated video


Logo
Put logo.png (and optionally logo.ico) next to the app, or use View ▸ Change Logo....

Author: Md. Rahatul Islam
