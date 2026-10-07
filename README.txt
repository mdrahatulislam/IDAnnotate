Rahat Label Studio - Fixed Tracking Version

Main fix:
- Prevents OpenCV tracker drift from blindly assigning an Individual ID to another person.
- Uses tracker prediction + local template matching + HSV appearance + motion/size validation.
- Stops propagation when confidence becomes too low instead of creating unreliable boxes.

Run:
python -m pip install -r requirements.txt
python rahat_label_studio.py
