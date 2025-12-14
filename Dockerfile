# CanvasL Logos System Docker Container
FROM node:18-alpine

# Install Coq for formal verification
RUN apk add --no-cache \
    coq \
    make \
    gcc \
    musl-dev

WORKDIR /app

# Copy package files first for better Docker layer caching
COPY package*.json ./
COPY logos-system/package*.json ./logos-system/

# Install dependencies
WORKDIR /app/logos-system
RUN npm ci --only=production

# Copy source code
COPY logos-system/ ./

# Build the project
RUN npm run build

# Copy formal verification files
COPY logos-system/formal/ ./formal/

# Verify formal proofs
RUN cd formal && make verify

# Create non-root user for security
RUN addgroup -g 1001 -S nodejs
RUN adduser -S nodejs -u 1001

# Change ownership of the app directory
RUN chown -R nodejs:nodejs /app
USER nodejs

# Expose port for potential web interface
EXPOSE 8080

# Set default command
CMD ["npm", "start"]