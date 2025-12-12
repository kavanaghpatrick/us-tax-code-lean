#!/bin/bash
# Monitor the Aristotle pilot run

echo "======================================"
echo "ARISTOTLE PILOT MONITOR"
echo "======================================"
echo ""

# Check if pilot is running
if pgrep -f "aristotle_formalization_queue.py --pilot" > /dev/null; then
    echo "✓ Pilot is RUNNING"
else
    echo "✗ Pilot is NOT running"
fi
echo ""

# Show queue status
if [ -f data/aristotle_queue.json ]; then
    echo "--- Queue Status ---"
    python3 << 'EOF'
import json
with open('data/aristotle_queue.json') as f:
    data = json.load(f)
    sections = data.get('sections', {})
    print(f"Total sections tracked: {len(sections)}")

    for sec, info in sections.items():
        status = info.get('status', 'unknown')
        print(f"  §{sec}: {status.upper()}")
        if 'project_id' in info:
            print(f"    Project: {info['project_id'][:8]}...")
        if 'time_taken_seconds' in info:
            mins = int(info['time_taken_seconds']) // 60
            print(f"    Time: {mins} minutes")
EOF
    echo ""
fi

# Check Aristotle API status
echo "--- Aristotle Projects ---"
python3 scripts/comprehensive_status.py 2>/dev/null | grep -A 5 "QUEUED\|IN_PROGRESS" || echo "No active projects"
echo ""

# Show recent output
echo "--- Recent Output (last 20 lines) ---"
tail -20 /tmp/claude/tasks/bb1685d.output 2>/dev/null || echo "No output yet..."
echo ""

echo "======================================"
echo "Monitor again: bash scripts/monitor_pilot.sh"
echo "======================================"
