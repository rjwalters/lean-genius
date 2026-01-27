#!/bin/bash
# archive-sessions.sh - Archive old sessions from knowledge.md
#
# Usage: ./archive-sessions.sh <problem-id> [--keep N]
#
# Archives sessions from knowledge.md to sessions/ subdirectory,
# keeping only the last N sessions (default 5) in the main file.

set -e

PROBLEM_ID="${1:-}"
KEEP_COUNT="${2:-5}"

if [[ -z "$PROBLEM_ID" ]]; then
    echo "Usage: $0 <problem-id> [--keep N]"
    echo "Example: $0 pnp-barriers"
    exit 1
fi

# Handle --keep flag
if [[ "$KEEP_COUNT" == "--keep" ]]; then
    KEEP_COUNT="${3:-5}"
fi

PROBLEM_DIR="research/problems/${PROBLEM_ID}"
KNOWLEDGE_FILE="${PROBLEM_DIR}/knowledge.md"
SESSIONS_DIR="${PROBLEM_DIR}/sessions"

if [[ ! -f "$KNOWLEDGE_FILE" ]]; then
    echo "Error: $KNOWLEDGE_FILE not found"
    exit 1
fi

# Create sessions directory if it doesn't exist
mkdir -p "$SESSIONS_DIR"

# Count current sessions (lines starting with "## Session")
SESSION_COUNT=$(grep -c "^## Session" "$KNOWLEDGE_FILE" 2>/dev/null || echo "0")

echo "Found $SESSION_COUNT sessions in $KNOWLEDGE_FILE"

if [[ "$SESSION_COUNT" -le "$KEEP_COUNT" ]]; then
    echo "Only $SESSION_COUNT sessions found, keeping all (threshold: $KEEP_COUNT)"
    exit 0
fi

# Calculate how many to archive
ARCHIVE_COUNT=$((SESSION_COUNT - KEEP_COUNT))
echo "Archiving $ARCHIVE_COUNT sessions, keeping $KEEP_COUNT"

# Extract sessions to archive
# Strategy: Find session boundaries and extract older ones

# Get line numbers of all session headers
SESSION_LINES=$(grep -n "^## Session" "$KNOWLEDGE_FILE" | head -n "$ARCHIVE_COUNT" | cut -d: -f1)

# For each session to archive, extract to individual file
PREV_END=0
SESSION_NUM=1
for LINE in $SESSION_LINES; do
    # Find the end of this session (next session or end of file)
    NEXT_SESSION=$(grep -n "^## Session" "$KNOWLEDGE_FILE" | awk -F: -v line="$LINE" '$1 > line {print $1; exit}')

    if [[ -z "$NEXT_SESSION" ]]; then
        # This shouldn't happen for sessions we're archiving, but handle it
        NEXT_SESSION=$(wc -l < "$KNOWLEDGE_FILE")
        ((NEXT_SESSION++))
    fi

    # Get session date from the header
    SESSION_HEADER=$(sed -n "${LINE}p" "$KNOWLEDGE_FILE")
    SESSION_DATE=$(echo "$SESSION_HEADER" | grep -oE '[0-9]{4}-[0-9]{2}-[0-9]{2}' | head -1 || echo "unknown")

    # Create archive filename
    ARCHIVE_FILE="${SESSIONS_DIR}/${SESSION_DATE}-s$(printf "%02d" $SESSION_NUM).md"

    # Extract session content
    END_LINE=$((NEXT_SESSION - 1))
    sed -n "${LINE},${END_LINE}p" "$KNOWLEDGE_FILE" > "$ARCHIVE_FILE"

    echo "Archived: $ARCHIVE_FILE"

    PREV_END=$END_LINE
    ((SESSION_NUM++))
done

# Now remove archived sessions from main file
# Find the line number of the first session we're keeping
FIRST_KEEP_LINE=$(grep -n "^## Session" "$KNOWLEDGE_FILE" | tail -n "$KEEP_COUNT" | head -1 | cut -d: -f1)

if [[ -n "$FIRST_KEEP_LINE" ]]; then
    # Get everything before the first archived session and after the last archived
    # Find line before first session header (the problem summary)
    FIRST_SESSION_LINE=$(grep -n "^## Session" "$KNOWLEDGE_FILE" | head -1 | cut -d: -f1)

    if [[ "$FIRST_SESSION_LINE" -gt 1 ]]; then
        # Keep the header/summary part
        HEADER_END=$((FIRST_SESSION_LINE - 1))
        head -n "$HEADER_END" "$KNOWLEDGE_FILE" > "${KNOWLEDGE_FILE}.tmp"

        # Add a note about archived sessions
        echo "" >> "${KNOWLEDGE_FILE}.tmp"
        echo "---" >> "${KNOWLEDGE_FILE}.tmp"
        echo "" >> "${KNOWLEDGE_FILE}.tmp"
        echo "> **Note**: $ARCHIVE_COUNT older sessions archived to \`sessions/\` directory." >> "${KNOWLEDGE_FILE}.tmp"
        echo "" >> "${KNOWLEDGE_FILE}.tmp"

        # Add the kept sessions
        FIRST_KEEP_LINE=$((FIRST_KEEP_LINE - 1))
        tail -n +"$FIRST_KEEP_LINE" "$KNOWLEDGE_FILE" | tail -n +2 >> "${KNOWLEDGE_FILE}.tmp"

        mv "${KNOWLEDGE_FILE}.tmp" "$KNOWLEDGE_FILE"

        echo "Updated $KNOWLEDGE_FILE - kept last $KEEP_COUNT sessions"
    fi
fi

echo "Done! Archived $ARCHIVE_COUNT sessions to $SESSIONS_DIR"
